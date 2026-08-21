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

bool isInteger(const VType &T) {
  return T.Kind == VTypeKind::Int32 || T.Kind == VTypeKind::Int64;
}

bool sameIntegerRepresentation(const VType &L, const VType &R) {
  return L.Kind == R.Kind && L.IntMode == R.IntMode &&
         L.IsSigned == R.IsSigned && L.BitWidth == R.BitWidth;
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

VType mathOffsetType() { return VType::makeInt(VIntMode::Math, 64, true); }

std::unique_ptr<VExpr> mathValue(const VExpr *E) {
  if (!E)
    return nullptr;
  VType MathTy = E->Ty;
  MathTy.IntMode = VIntMode::Math;
  if (E->Ty.IntMode == VIntMode::Math)
    return cloneVExpr(E);
  return std::make_unique<VCastExpr>(cloneVExpr(E), E->Ty, MathTy, E->Loc);
}

const VExpr *machineValueInsideMathCast(const VExpr *E) {
  if (!E || E->K != VExpr::Cast)
    return nullptr;
  const auto *Cast = static_cast<const VCastExpr *>(E);
  if (Cast->FromTy.IntMode != VIntMode::Machine ||
      Cast->Ty.IntMode != VIntMode::Math)
    return nullptr;
  return Cast->Inner.get();
}

std::unique_ptr<VExpr> unscalePointerOffset(const VExpr *E,
                                            uint64_t PointeeSize) {
  if (!E || PointeeSize == 0)
    return nullptr;
  if (PointeeSize == 1) {
    if (const VExpr *Machine = machineValueInsideMathCast(E))
      return cloneVExpr(Machine);
    return cloneVExpr(E);
  }
  if (E->K != VExpr::BinOp)
    return nullptr;
  const auto *Mul = static_cast<const VBinOpExpr *>(E);
  if (Mul->Op != VBinOp::Mul)
    return nullptr;
  auto IsStride = [PointeeSize](const VExpr *Candidate) {
    return Candidate && Candidate->K == VExpr::Literal &&
           static_cast<const VLiteralExpr *>(Candidate)->Value ==
               std::to_string(PointeeSize);
  };
  if (IsStride(Mul->Rhs.get()))
    if (const VExpr *Machine = machineValueInsideMathCast(Mul->Lhs.get()))
      return cloneVExpr(Machine);
  if (IsStride(Mul->Lhs.get()))
    if (const VExpr *Machine = machineValueInsideMathCast(Mul->Rhs.get()))
      return cloneVExpr(Machine);
  return nullptr;
}

bool isPointerBase(const VExpr *E, const std::string &Base) {
  while (E && E->K == VExpr::Cast)
    E = static_cast<const VCastExpr *>(E)->Inner.get();
  return E && E->K == VExpr::Var &&
         static_cast<const VVarExpr *>(E)->Name == Base;
}

const VExpr *directPointerVariable(const VExpr *E) {
  while (E && E->K == VExpr::Cast)
    E = static_cast<const VCastExpr *>(E)->Inner.get();
  return E && E->K == VExpr::Var && E->Ty.Kind == VTypeKind::Ptr ? E : nullptr;
}

bool containsValidCall(const VExpr *E) {
  if (!E)
    return false;
  switch (E->K) {
  case VExpr::Literal:
  case VExpr::Var:
  case VExpr::Result:
    return false;
  case VExpr::BinOp: {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    return containsValidCall(B->Lhs.get()) || containsValidCall(B->Rhs.get());
  }
  case VExpr::UnaryOp:
    return containsValidCall(
        static_cast<const VUnaryOpExpr *>(E)->Operand.get());
  case VExpr::Cast:
    return containsValidCall(static_cast<const VCastExpr *>(E)->Inner.get());
  case VExpr::Load:
    return containsValidCall(static_cast<const VLoadExpr *>(E)->Ptr.get());
  case VExpr::Old:
    return containsValidCall(static_cast<const VOldExpr *>(E)->Inner.get());
  case VExpr::Conditional: {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    return containsValidCall(C->Cond.get()) ||
           containsValidCall(C->Then.get()) || containsValidCall(C->Else.get());
  }
  case VExpr::Forall:
  case VExpr::Exists: {
    const auto *Q = static_cast<const VQuantifiedExpr *>(E);
    return containsValidCall(Q->Lo.get()) || containsValidCall(Q->Hi.get()) ||
           containsValidCall(Q->Body.get());
  }
  case VExpr::HeapStore: {
    const auto *S = static_cast<const VHeapStoreExpr *>(E);
    return containsValidCall(S->Ptr.get()) || containsValidCall(S->Val.get());
  }
  case VExpr::FieldAccess:
    return containsValidCall(
        static_cast<const VFieldAccessExpr *>(E)->Base.get());
  case VExpr::SpecCall: {
    const auto *C = static_cast<const VSpecCallExpr *>(E);
    if (C->Callee == "valid")
      return true;
    for (const auto &Arg : C->Args)
      if (containsValidCall(Arg.get()))
        return true;
    return false;
  }
  case VExpr::OverflowCheck: {
    const auto *O = static_cast<const VOverflowCheckExpr *>(E);
    return containsValidCall(O->Lhs.get()) || containsValidCall(O->Rhs.get());
  }
  }
  return false;
}

std::unique_ptr<VExpr> directElementOffset(const VExpr *Addr,
                                           const std::string &Base,
                                           uint64_t PointeeSize,
                                           const VType &IndexType) {
  while (Addr && Addr->K == VExpr::Cast)
    Addr = static_cast<const VCastExpr *>(Addr)->Inner.get();
  if (isPointerBase(Addr, Base))
    return std::make_unique<VLiteralExpr>(0, IndexType, Addr->Loc);
  if (!Addr || Addr->K != VExpr::BinOp)
    return nullptr;
  const auto *Add = static_cast<const VBinOpExpr *>(Addr);
  if (Add->Op != VBinOp::Add)
    return nullptr;
  if (isPointerBase(Add->Lhs.get(), Base))
    return unscalePointerOffset(Add->Rhs.get(), PointeeSize);
  if (isPointerBase(Add->Rhs.get(), Base))
    return unscalePointerOffset(Add->Lhs.get(), PointeeSize);
  return nullptr;
}

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

// The target-byte offset of an address relative to its base pointer: bare `p`
// becomes zero and typed pointer steps are already stride-scaled. Returns null
// if Addr is not a base(+/-)offset form rooted at Base.
std::unique_ptr<VExpr> pointerOffset(const VExpr *Addr,
                                     const std::string &Base) {
  if (!Addr)
    return nullptr;
  if (Addr->K == VExpr::Cast)
    return pointerOffset(static_cast<const VCastExpr *>(Addr)->Inner.get(),
                         Base);
  if (Addr->K == VExpr::Var) {
    if (static_cast<const VVarExpr *>(Addr)->Name == Base)
      return std::make_unique<VLiteralExpr>(0, mathOffsetType(), Addr->Loc);
    return nullptr;
  }
  if (Addr->K == VExpr::BinOp) {
    const auto *B = static_cast<const VBinOpExpr *>(Addr);
    if (B->Op == VBinOp::Add || B->Op == VBinOp::Sub) {
      if (auto LO = pointerOffset(B->Lhs.get(), Base))
        return std::make_unique<VBinOpExpr>(B->Op, std::move(LO),
                                            cloneVExpr(B->Rhs.get()),
                                            mathOffsetType(), B->Loc);
      if (B->Op == VBinOp::Add)
        if (auto RO = pointerOffset(B->Rhs.get(), Base))
          return std::make_unique<VBinOpExpr>(
              VBinOp::Add, cloneVExpr(B->Lhs.get()), std::move(RO),
              mathOffsetType(), B->Loc);
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
  std::map<std::string, uint64_t> ValidPointeeSize;
  std::optional<std::string> Error;

  // A marker is meaningful only as a positive top-level conjunction clause.
  void scanValid(const VExpr *E) {
    if (!E)
      return;
    if (E->K == VExpr::BinOp) {
      const auto *B = static_cast<const VBinOpExpr *>(E);
      if (B->Op == VBinOp::And) {
        scanValid(B->Lhs.get());
        scanValid(B->Rhs.get());
        return;
      }
    }
    if (E->K == VExpr::SpecCall) {
      const auto *C = static_cast<const VSpecCallExpr *>(E);
      if (C->Callee != "valid") {
        if (containsValidCall(E))
          Error =
              "valid marker must be a positive top-level conjunction clause";
        return;
      }
      if (C->Args.size() != 2) {
        Error = "valid marker must have exactly two arguments";
        return;
      }
      const VExpr *Base = directPointerVariable(C->Args[0].get());
      const VType &LengthType = C->Args[1]->Ty;
      if (!Base || !isInteger(LengthType) || Base->Ty.PointeeSizeBytes == 0) {
        Error = "valid marker requires a bare complete-object pointer and an "
                "integer element count";
        return;
      }
      const std::string &Name = static_cast<const VVarExpr *>(Base)->Name;
      if (ValidLen.count(Name)) {
        Error = "multiple valid markers for the same pointer are unsupported";
        return;
      }
      ValidLen[Name] = C->Args[1].get();
      ValidPointeeSize[Name] = Base->Ty.PointeeSizeBytes;
      return;
    }
    if (containsValidCall(E))
      Error = "valid marker must be a positive top-level conjunction clause";
  }

  void appendValidSemantics(VFunction &Fn) const {
    for (const auto &[Base, Length] : ValidLen) {
      SourceLocation Loc = Length->Loc;
      const uint64_t PointeeSize = ValidPointeeSize.at(Base);
      VType PointerType = VType::makePtr(PointeeSize);
      Fn.ValidExtents.emplace_back(Base, PointerType, cloneVExpr(Length));
      auto Pointer = std::make_unique<VVarExpr>(Base, PointerType, Loc);
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

  // Bounds obligation for an access at Addr when the base pointer has a
  // declared element count; null when no extent applies.
  std::unique_ptr<VExpr> boundsObligation(const VExpr *Addr) {
    const VExpr *B = pointerBase(Addr);
    if (!B || B->K != VExpr::Var)
      return nullptr;
    auto It = ValidLen.find(static_cast<const VVarExpr *>(B)->Name);
    if (It == ValidLen.end())
      return nullptr;
    const std::string &Base = static_cast<const VVarExpr *>(B)->Name;
    const auto SizeIt = ValidPointeeSize.find(Base);
    if (SizeIt == ValidPointeeSize.end() || SizeIt->second == 0)
      return std::make_unique<VLiteralExpr>(false, VType::makeBool(),
                                            Addr->Loc);
    const uint64_t PointeeSize = SizeIt->second;
    if (auto ElementOffset =
            directElementOffset(Addr, Base, PointeeSize, It->second->Ty)) {
      if (sameIntegerRepresentation(ElementOffset->Ty, It->second->Ty)) {
        auto Ge = std::make_unique<VBinOpExpr>(
            VBinOp::Ge, cloneVExpr(ElementOffset.get()),
            std::make_unique<VLiteralExpr>(0, ElementOffset->Ty, Addr->Loc),
            VType::makeBool(), Addr->Loc);
        auto Lt = std::make_unique<VBinOpExpr>(
            VBinOp::Lt, std::move(ElementOffset), cloneVExpr(It->second),
            VType::makeBool(), Addr->Loc);
        return std::make_unique<VBinOpExpr>(VBinOp::And, std::move(Ge),
                                            std::move(Lt), VType::makeBool(),
                                            Addr->Loc);
      }
    }
    auto Off = pointerOffset(Addr, static_cast<const VVarExpr *>(B)->Name);
    if (!Off)
      return nullptr;
    SourceLocation Loc = Addr->Loc;
    auto Limit = mathValue(It->second);
    if (!Limit)
      return std::make_unique<VLiteralExpr>(false, VType::makeBool(), Loc);
    if (PointeeSize > 1) {
      VType MathTy = Limit->Ty;
      auto Stride = std::make_unique<VLiteralExpr>(std::to_string(PointeeSize),
                                                   MathTy, Loc);
      Limit = std::make_unique<VBinOpExpr>(VBinOp::Mul, std::move(Limit),
                                           std::move(Stride), MathTy, Loc);
    }
    auto Ge = std::make_unique<VBinOpExpr>(
        VBinOp::Ge, cloneVExpr(Off.get()),
        std::make_unique<VLiteralExpr>(0, mathOffsetType(), Loc),
        VType::makeBool(), Loc);
    auto Lt = std::make_unique<VBinOpExpr>(
        VBinOp::Lt, std::move(Off), std::move(Limit), VType::makeBool(), Loc);
    return std::make_unique<VBinOpExpr>(VBinOp::And, std::move(Ge),
                                        std::move(Lt), VType::makeBool(), Loc);
  }

  static std::unique_ptr<VExpr> evaluationGuard(const VExpr *Parent,
                                                std::unique_ptr<VExpr> Local,
                                                SourceLocation Loc) {
    if (!Parent)
      return Local;
    return std::make_unique<VBinOpExpr>(VBinOp::And, cloneVExpr(Parent),
                                        std::move(Local), VType::makeBool(),
                                        Loc);
  }

  static void appendObligation(std::unique_ptr<VExpr> Obligation,
                               const VExpr *Guard,
                               std::vector<std::unique_ptr<VExpr>> &Out) {
    if (Guard) {
      SourceLocation Loc = Obligation->Loc;
      auto NotGuard = std::make_unique<VUnaryOpExpr>(
          VUnaryOp::Not, cloneVExpr(Guard), VType::makeBool(), Loc);
      Obligation = std::make_unique<VBinOpExpr>(VBinOp::Or, std::move(NotGuard),
                                                std::move(Obligation),
                                                VType::makeBool(), Loc);
    }
    Out.push_back(std::move(Obligation));
  }

  // Walk E and append safety obligations under the exact C++ evaluation path.
  void collectObligations(const VExpr *E,
                          std::vector<std::unique_ptr<VExpr>> &Out,
                          const VExpr *Guard = nullptr) {
    if (!E)
      return;
    switch (E->K) {
    case VExpr::BinOp: {
      const auto *B = static_cast<const VBinOpExpr *>(E);
      collectObligations(B->Lhs.get(), Out, Guard);
      if (B->Op == VBinOp::And || B->Op == VBinOp::Or) {
        std::unique_ptr<VExpr> RhsCondition = cloneVExpr(B->Lhs.get());
        if (B->Op == VBinOp::Or)
          RhsCondition = std::make_unique<VUnaryOpExpr>(
              VUnaryOp::Not, std::move(RhsCondition), VType::makeBool(),
              B->Loc);
        auto RhsGuard = evaluationGuard(Guard, std::move(RhsCondition), B->Loc);
        collectObligations(B->Rhs.get(), Out, RhsGuard.get());
      } else {
        collectObligations(B->Rhs.get(), Out, Guard);
      }
      const bool Signed = isSignedMachine(B->Ty);
      switch (B->Op) {
      case VBinOp::Add:
        if (Signed)
          appendObligation(
              mkOvf(VOverflowOp::Add, B->Lhs.get(), B->Rhs.get(), B->Loc),
              Guard, Out);
        break;
      case VBinOp::Sub:
        if (Signed)
          appendObligation(
              mkOvf(VOverflowOp::Sub, B->Lhs.get(), B->Rhs.get(), B->Loc),
              Guard, Out);
        break;
      case VBinOp::Mul:
        if (Signed)
          appendObligation(
              mkOvf(VOverflowOp::Mul, B->Lhs.get(), B->Rhs.get(), B->Loc),
              Guard, Out);
        break;
      case VBinOp::Div:
      case VBinOp::Rem:
        if (isMachineInt(B->Ty))
          appendObligation(mkNonZero(B->Rhs.get(), B->Loc), Guard, Out);
        if (Signed)
          appendObligation(
              mkOvf(VOverflowOp::SDiv, B->Lhs.get(), B->Rhs.get(), B->Loc),
              Guard, Out);
        break;
      default:
        break;
      }
      break;
    }
    case VExpr::UnaryOp: {
      const auto *U = static_cast<const VUnaryOpExpr *>(E);
      collectObligations(U->Operand.get(), Out, Guard);
      if (U->Op == VUnaryOp::Neg && isSignedMachine(U->Ty))
        appendObligation(
            mkOvf(VOverflowOp::Neg, U->Operand.get(), nullptr, U->Loc), Guard,
            Out);
      break;
    }
    case VExpr::Cast:
      collectObligations(static_cast<const VCastExpr *>(E)->Inner.get(), Out,
                         Guard);
      break;
    case VExpr::Conditional: {
      const auto *C = static_cast<const VConditionalExpr *>(E);
      collectObligations(C->Cond.get(), Out, Guard);
      auto ThenGuard =
          evaluationGuard(Guard, cloneVExpr(C->Cond.get()), C->Loc);
      auto NotCondition = std::make_unique<VUnaryOpExpr>(
          VUnaryOp::Not, cloneVExpr(C->Cond.get()), VType::makeBool(), C->Loc);
      auto ElseGuard = evaluationGuard(Guard, std::move(NotCondition), C->Loc);
      collectObligations(C->Then.get(), Out, ThenGuard.get());
      collectObligations(C->Else.get(), Out, ElseGuard.get());
      break;
    }
    case VExpr::Load: {
      // Array-bounds: a read through p[i] / *(p+i) must be in [0, len(p)).
      const auto *L = static_cast<const VLoadExpr *>(E);
      collectObligations(L->Ptr.get(), Out, Guard);
      collectObligations(L->AccessCondition.get(), Out, Guard);
      if (auto Bnd = boundsObligation(L->Ptr.get()))
        appendObligation(std::move(Bnd), Guard, Out);
      break;
    }
    case VExpr::FieldAccess:
      collectObligations(static_cast<const VFieldAccessExpr *>(E)->Base.get(),
                         Out, Guard);
      break;
    case VExpr::Old:
      collectObligations(static_cast<const VOldExpr *>(E)->Inner.get(), Out,
                         Guard);
      break;
    case VExpr::SpecCall: {
      const auto *S = static_cast<const VSpecCallExpr *>(E);
      for (const auto &A : S->Args)
        collectObligations(A.get(), Out, Guard);
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
        emitObsInto(New, St.AccessCondition.get());
        break;
      }
      case VStmt::Allocate:
        if (const auto &A = static_cast<VAllocateStmt &>(*S); A.Initializer)
          emitObsInto(New, A.Initializer.get());
        break;
      case VStmt::EndLifetime:
        break;
      case VStmt::Free:
        emitObsInto(New, static_cast<VFreeStmt &>(*S).Ptr.get());
        break;
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

bool verify::usesValidMarker(const VFunction &Fn) {
  if (Fn.IsSpec)
    return false;
  for (const auto &Pre : Fn.Preconditions)
    if (containsValidCall(Pre.get()))
      return true;
  for (const auto &Post : Fn.Postconditions)
    if (containsValidCall(Post.get()))
      return true;
  return false;
}

std::optional<std::string> verify::instrumentUBChecks(VFunction &Fn) {
  if (Fn.IsSpec)
    return std::nullopt;
  UBInstrumenter UB;
  for (const auto &Pre : Fn.Preconditions)
    UB.scanValid(Pre.get());
  if (UB.Error)
    return UB.Error;
  UB.appendValidSemantics(Fn);
  UB.instrumentStmts(Fn.Body);
  return std::nullopt;
}
