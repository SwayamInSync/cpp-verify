//===--- UBChecks.cpp - Layer-A undefined-behavior obligations -------------===//
#include "UBChecks.h"
#include "../IR/VExpr.h"

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
  return std::make_unique<VOverflowCheckExpr>(
      Op, cloneVExpr(L), R ? cloneVExpr(R) : nullptr, Loc);
}

// divisor != 0
std::unique_ptr<VExpr> mkNonZero(const VExpr *Divisor, SourceLocation Loc) {
  auto Zero = std::make_unique<VLiteralExpr>(0, Divisor->Ty, Loc);
  return std::make_unique<VBinOpExpr>(VBinOp::Ne, cloneVExpr(Divisor),
                                      std::move(Zero), VType::makeBool(), Loc);
}

//===----------------------------------------------------------------------===//
// The checker registry: walk an expression and append safety obligations.
// Each obligation is a boolean VExpr that is true iff the operation is safe.
// Children are visited first so nested operations are also covered; all
// obligations are independent asserts, so their relative order is irrelevant.
// To add a UB class, add a case here (and, if it needs a solver primitive, a
// node + encoder case). See docs/UB-CHECKING.md.
//===----------------------------------------------------------------------===//
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
        Out.push_back(mkOvf(VOverflowOp::Add, B->Lhs.get(), B->Rhs.get(), B->Loc));
      break;
    case VBinOp::Sub:
      if (Signed)
        Out.push_back(mkOvf(VOverflowOp::Sub, B->Lhs.get(), B->Rhs.get(), B->Loc));
      break;
    case VBinOp::Mul:
      if (Signed)
        Out.push_back(mkOvf(VOverflowOp::Mul, B->Lhs.get(), B->Rhs.get(), B->Loc));
      break;
    case VBinOp::Div:
    case VBinOp::Rem:
      // Division/modulo by zero is UB for both signed and unsigned.
      if (isMachineInt(B->Ty))
        Out.push_back(mkNonZero(B->Rhs.get(), B->Loc));
      // INT_MIN / -1 (and the modulo equivalent) overflows for signed.
      if (Signed)
        Out.push_back(mkOvf(VOverflowOp::SDiv, B->Lhs.get(), B->Rhs.get(), B->Loc));
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
      Out.push_back(mkOvf(VOverflowOp::Neg, U->Operand.get(), nullptr, U->Loc));
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
  case VExpr::Load:
    collectObligations(static_cast<const VLoadExpr *>(E)->Ptr.get(), Out);
    break;
  case VExpr::FieldAccess:
    collectObligations(static_cast<const VFieldAccessExpr *>(E)->Base.get(), Out);
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
  // Literal, Var, Result, quantifiers, HeapStore, OverflowCheck: no obligation.
  default:
    break;
  }
}

// Append the obligation asserts for expression E into the statement list.
void emitObsInto(std::vector<std::unique_ptr<VStmt>> &Out, const VExpr *E) {
  std::vector<std::unique_ptr<VExpr>> Obs;
  collectObligations(E, Obs);
  for (auto &O : Obs) {
    SourceLocation L = O->Loc;
    Out.push_back(std::make_unique<VContractAssertStmt>(std::move(O), L));
  }
}

// Walk a statement list, inserting obligation asserts before each statement in
// evaluation order. Recurses into nested control flow. Ghost/spec statements and
// contract expressions are not executed at runtime and are left untouched.
void instrumentStmts(std::vector<std::unique_ptr<VStmt>> &Stmts) {
  std::vector<std::unique_ptr<VStmt>> New;
  for (auto &S : Stmts) {
    switch (S->K) {
    case VStmt::Assign:
      emitObsInto(New, static_cast<VAssignStmt &>(*S).Value.get());
      break;
    case VStmt::Store: {
      auto &St = static_cast<VStoreStmt &>(*S);
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
      // The condition is evaluated once on entry (here, concrete pre-state) ...
      emitObsInto(New, W.Cond.get());
      instrumentStmts(W.Body);
      // ... and again after each iteration: check it at the end of the body, in
      // the inductive (havocked) context.
      std::vector<std::unique_ptr<VExpr>> CondObs;
      collectObligations(W.Cond.get(), CondObs);
      for (auto &O : CondObs) {
        SourceLocation L = O->Loc;
        W.Body.push_back(std::make_unique<VContractAssertStmt>(std::move(O), L));
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
    // Ghost/spec/contract statements are not executed → no runtime UB.
    default:
      break;
    }
    New.push_back(std::move(S));
  }
  Stmts = std::move(New);
}

} // namespace

void verify::instrumentUBChecks(VFunction &Fn) {
  if (Fn.IsSpec)
    return;
  instrumentStmts(Fn.Body);
}
