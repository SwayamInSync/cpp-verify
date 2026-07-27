//===--- UBChecks.cpp - UB and bounds obligations -------------------------===//
#include "UBChecks.h"
#include "../IR/VExpr.h"
#include <map>

using namespace clang;
using namespace verify;

namespace {

// Only signed machine integers can overflow into UB; unsigned is modular and
// well-defined in C++.
bool isSignedMachine(const VType &T) {
  return T.IntMode == VIntMode::Machine && T.isSignedInt();
}
bool isMachineInt(const VType &T) {
  return T.IntMode == VIntMode::Machine &&
         (T.Kind == VTypeKind::Int32 || T.Kind == VTypeKind::Int64);
}

std::unique_ptr<VExpr> mkOvf(VOverflowOp Op, const VExpr *L, const VExpr *R,
                             SourceLocation Loc) {
  return std::make_unique<VOverflowCheckExpr>(Op, cloneVExpr(L),
                                              R ? cloneVExpr(R) : nullptr, Loc);
}

// divisor != 0
std::unique_ptr<VExpr> mkNonZero(const VExpr *Divisor, SourceLocation Loc) {
  auto Zero = std::make_unique<VLiteralExpr>(0, Divisor->Ty, Loc);
  return std::make_unique<VBinOpExpr>(VBinOp::Ne, cloneVExpr(Divisor),
                                      std::move(Zero), VType::makeBool(), Loc);
}

VType machineInt(SourceLocation) { return VType::makeInt32(VIntMode::Machine); }

// The base pointer an address is rooted at: strips casts and pointer arithmetic
// (`p + i` -> `p`). Returns a Var when the root is a named pointer.
const VExpr *pointerBase(const VExpr *E) {
  if (!E)
    return nullptr;
  switch (E->K) {
  case VExpr::Cast:
    return pointerBase(static_cast<const VCastExpr *>(E)->Inner.get());
  case VExpr::Load:
    return pointerBase(static_cast<const VLoadExpr *>(E)->Ptr.get());
  case VExpr::BinOp: {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    if (B->Op == VBinOp::Add || B->Op == VBinOp::Sub) {
      if (const VExpr *L = pointerBase(B->Lhs.get()); L && L->K == VExpr::Var)
        return L;
      if (const VExpr *R = pointerBase(B->Rhs.get()); R && R->K == VExpr::Var)
        return R;
    }
    return E;
  }
  default:
    return E;
  }
}

// The machine-integer offset of an address relative to its base pointer: `p +
// i`
// -> `i`, bare `p` -> `0`. Returns null if Addr isn't of base(+/-)offset form
// rooted at Base.
std::unique_ptr<VExpr> pointerOffset(const VExpr *Addr,
                                     const std::string &Base) {
  if (!Addr)
    return nullptr;
  if (Addr->K == VExpr::Cast)
    return pointerOffset(static_cast<const VCastExpr *>(Addr)->Inner.get(),
                         Base);
  if (Addr->K == VExpr::Var) {
    if (static_cast<const VVarExpr *>(Addr)->Name == Base)
      return std::make_unique<VLiteralExpr>(0, machineInt(Addr->Loc),
                                            Addr->Loc);
    return nullptr;
  }
  if (Addr->K == VExpr::BinOp) {
    const auto *B = static_cast<const VBinOpExpr *>(Addr);
    if (B->Op == VBinOp::Add || B->Op == VBinOp::Sub) {
      if (auto LO = pointerOffset(B->Lhs.get(), Base))
        return std::make_unique<VBinOpExpr>(B->Op, std::move(LO),
                                            cloneVExpr(B->Rhs.get()),
                                            machineInt(B->Loc), B->Loc);
      if (B->Op == VBinOp::Add)
        if (auto RO = pointerOffset(B->Rhs.get(), Base))
          return std::make_unique<VBinOpExpr>(
              VBinOp::Add, cloneVExpr(B->Lhs.get()), std::move(RO),
              machineInt(B->Loc), B->Loc);
    }
  }
  return nullptr;
}

//===----------------------------------------------------------------------===//
// The checker. Holds the declared buffer lengths (from `valid(p, n)`
// preconditions) so array accesses get bounds obligations, and emits the
// arithmetic obligations (overflow, division). See docs/UB-CHECKING.md.
//===----------------------------------------------------------------------===//
struct UBInstrumenter {
  // base pointer name -> its declared length (from `valid(p, n)`).
  std::map<std::string, const VExpr *> ValidLen;

  // Scan a precondition for `valid(p, n)` declarations (recursing through
  // `&&`).
  void scanValid(const VExpr *E) {
    if (!E)
      return;
    if (E->K == VExpr::SpecCall) {
      const auto *C = static_cast<const VSpecCallExpr *>(E);
      if (C->Callee == "valid" && C->Args.size() == 2) {
        const VExpr *B = pointerBase(C->Args[0].get());
        if (B && B->K == VExpr::Var)
          ValidLen[static_cast<const VVarExpr *>(B)->Name] = C->Args[1].get();
      }

      return;
    }
    if (E->K == VExpr::BinOp) {
      const auto *B = static_cast<const VBinOpExpr *>(E);
      scanValid(B->Lhs.get());
      scanValid(B->Rhs.get());
    }
  }

  void appendValidSemantics(VFunction &Fn) const {
    for (const auto &[Base, Length] : ValidLen) {
      SourceLocation Loc = Length->Loc;
      auto Pointer = std::make_unique<VVarExpr>(Base, VType::makePtr(), Loc);
      auto NonNegative = std::make_unique<VBinOpExpr>(
          VBinOp::Ge, cloneVExpr(Length),
          std::make_unique<VLiteralExpr>(0, Length->Ty, Loc), VType::makeBool(),
          Loc);
      auto Empty = std::make_unique<VBinOpExpr>(
          VBinOp::Eq, cloneVExpr(Length),
          std::make_unique<VLiteralExpr>(0, Length->Ty, Loc), VType::makeBool(),
          Loc);
      auto NonNull = std::make_unique<VBinOpExpr>(
          VBinOp::Ne, cloneVExpr(Pointer.get()),
          std::make_unique<VLiteralExpr>(0, VType::makePtr(), Loc),
          VType::makeBool(), Loc);
      auto IsValid = std::make_unique<VUnaryOpExpr>(
          VUnaryOp::ValidPtr, std::move(Pointer), VType::makeBool(), Loc);
      auto NonEmptyValid = std::make_unique<VBinOpExpr>(
          VBinOp::And, std::move(NonNull), std::move(IsValid),
          VType::makeBool(), Loc);
      auto ValidExtent = std::make_unique<VBinOpExpr>(
          VBinOp::Or, std::move(Empty), std::move(NonEmptyValid),
          VType::makeBool(), Loc);
      Fn.Preconditions.push_back(std::make_unique<VBinOpExpr>(
          VBinOp::And, std::move(NonNegative), std::move(ValidExtent),
          VType::makeBool(), Loc));
    }
  }

  // Bounds obligation `0 <= off && off < len` for an access at Addr, when the
  // base pointer has a declared length; null otherwise.
  std::unique_ptr<VExpr> boundsObligation(const VExpr *Addr) {
    const VExpr *B = pointerBase(Addr);
    if (!B || B->K != VExpr::Var)
      return nullptr;
    auto It = ValidLen.find(static_cast<const VVarExpr *>(B)->Name);
    if (It == ValidLen.end())
      return nullptr;
    auto Off = pointerOffset(Addr, static_cast<const VVarExpr *>(B)->Name);
    if (!Off)
      return nullptr;
    SourceLocation Loc = Addr->Loc;
    auto Ge = std::make_unique<VBinOpExpr>(
        VBinOp::Ge, cloneVExpr(Off.get()),
        std::make_unique<VLiteralExpr>(0, machineInt(Loc), Loc),
        VType::makeBool(), Loc);
    auto Lt = std::make_unique<VBinOpExpr>(VBinOp::Lt, std::move(Off),
                                           cloneVExpr(It->second),
                                           VType::makeBool(), Loc);
    return std::make_unique<VBinOpExpr>(VBinOp::And, std::move(Ge),
                                        std::move(Lt), VType::makeBool(), Loc);
  }

  // Walk E, append safety obligations. To add a UB class, add a case here.
  void collectObligations(const VExpr *E,
                          std::vector<std::unique_ptr<VExpr>> &Out) {
    if (!E)
      return;
    switch (E->K) {
    case VExpr::BinOp: {
      const auto *B = static_cast<const VBinOpExpr *>(E);
      collectObligations(B->Lhs.get(), Out);
      collectObligations(B->Rhs.get(), Out);
      const bool Signed = isSignedMachine(B->Ty);
      switch (B->Op) {
      case VBinOp::Add:
        if (Signed)
          Out.push_back(
              mkOvf(VOverflowOp::Add, B->Lhs.get(), B->Rhs.get(), B->Loc));
        break;
      case VBinOp::Sub:
        if (Signed)
          Out.push_back(
              mkOvf(VOverflowOp::Sub, B->Lhs.get(), B->Rhs.get(), B->Loc));
        break;
      case VBinOp::Mul:
        if (Signed)
          Out.push_back(
              mkOvf(VOverflowOp::Mul, B->Lhs.get(), B->Rhs.get(), B->Loc));
        break;
      case VBinOp::Div:
      case VBinOp::Rem:
        if (isMachineInt(B->Ty))
          Out.push_back(mkNonZero(B->Rhs.get(), B->Loc));
        if (Signed)
          Out.push_back(
              mkOvf(VOverflowOp::SDiv, B->Lhs.get(), B->Rhs.get(), B->Loc));
        break;
      default:
        break;
      }
      break;
    }
    case VExpr::UnaryOp: {
      const auto *U = static_cast<const VUnaryOpExpr *>(E);
      collectObligations(U->Operand.get(), Out);
      if (U->Op == VUnaryOp::Neg && isSignedMachine(U->Ty))
        Out.push_back(
            mkOvf(VOverflowOp::Neg, U->Operand.get(), nullptr, U->Loc));
      break;
    }
    case VExpr::Cast:
      collectObligations(static_cast<const VCastExpr *>(E)->Inner.get(), Out);
      break;
    case VExpr::Conditional: {
      const auto *C = static_cast<const VConditionalExpr *>(E);
      collectObligations(C->Cond.get(), Out);
      collectObligations(C->Then.get(), Out);
      collectObligations(C->Else.get(), Out);
      break;
    }
    case VExpr::Load: {
      // Array-bounds: a read through p[i] / *(p+i) must be in [0, len(p)).
      const auto *L = static_cast<const VLoadExpr *>(E);
      collectObligations(L->Ptr.get(), Out);
      if (auto Bnd = boundsObligation(L->Ptr.get()))
        Out.push_back(std::move(Bnd));
      break;
    }
    case VExpr::FieldAccess:
      collectObligations(static_cast<const VFieldAccessExpr *>(E)->Base.get(),
                         Out);
      break;
    case VExpr::Old:
      collectObligations(static_cast<const VOldExpr *>(E)->Inner.get(), Out);
      break;
    case VExpr::SpecCall: {
      const auto *S = static_cast<const VSpecCallExpr *>(E);
      for (const auto &A : S->Args)
        collectObligations(A.get(), Out);
      break;
    }
    default:
      break;
    }
  }

  void emitObsInto(std::vector<std::unique_ptr<VStmt>> &Out, const VExpr *E) {
    std::vector<std::unique_ptr<VExpr>> Obs;
    collectObligations(E, Obs);
    for (auto &O : Obs) {
      SourceLocation L = O->Loc;
      Out.push_back(std::make_unique<VContractAssertStmt>(std::move(O), L));
    }
  }

  void instrumentStmts(std::vector<std::unique_ptr<VStmt>> &Stmts) {
    std::vector<std::unique_ptr<VStmt>> New;
    for (auto &S : Stmts) {
      switch (S->K) {
      case VStmt::Assign:
        emitObsInto(New, static_cast<VAssignStmt &>(*S).Value.get());
        break;
      case VStmt::Store: {
        auto &St = static_cast<VStoreStmt &>(*S);
        // Array-bounds for the write target p[j] = ...
        if (auto Bnd = boundsObligation(St.Ptr.get())) {
          SourceLocation L = Bnd->Loc;
          New.push_back(
              std::make_unique<VContractAssertStmt>(std::move(Bnd), L));
        }
        emitObsInto(New, St.Ptr.get());
        emitObsInto(New, St.Value.get());
        break;
      }
      case VStmt::Return:
        emitObsInto(New, static_cast<VReturnStmt &>(*S).Value.get());
        break;
      case VStmt::If: {
        auto &I = static_cast<VIfStmt &>(*S);
        emitObsInto(New, I.Cond.get());
        instrumentStmts(I.Then);
        instrumentStmts(I.Else);
        break;
      }
      case VStmt::While: {
        auto &W = static_cast<VWhileStmt &>(*S);
        emitObsInto(New, W.Cond.get());
        instrumentStmts(W.Body);
        std::vector<std::unique_ptr<VExpr>> CondObs;
        collectObligations(W.Cond.get(), CondObs);
        for (auto &O : CondObs) {
          SourceLocation L = O->Loc;
          W.Body.push_back(
              std::make_unique<VContractAssertStmt>(std::move(O), L));
        }
        break;
      }
      case VStmt::Call:
        for (const auto &A : static_cast<VCallStmt &>(*S).Args)
          emitObsInto(New, A.get());
        break;
      case VStmt::Seq:
        instrumentStmts(static_cast<VSeqStmt &>(*S).Stmts);
        break;
      default:
        break;
      }
      New.push_back(std::move(S));
    }
    Stmts = std::move(New);
  }
};

} // namespace

void verify::instrumentUBChecks(VFunction &Fn) {
  if (Fn.IsSpec)
    return;
  UBInstrumenter UB;
  for (const auto &Pre : Fn.Preconditions)
    UB.scanValid(Pre.get());
  UB.appendValidSemantics(Fn);
  UB.instrumentStmts(Fn.Body);
}
