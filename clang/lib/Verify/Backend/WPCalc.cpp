//===--- WPCalc.cpp -------------------------------------------------------===//
#include "WPCalc.h"

using namespace clang;
using namespace verify;

static std::unique_ptr<VExpr> cloneForVC(const VExpr *E);

static std::unique_ptr<VExpr> makeTrue(SourceLocation Loc) {
  return std::make_unique<VLiteralExpr>(1, VType::makeBool(), Loc);
}

static std::unique_ptr<VExpr> makeAnd(std::unique_ptr<VExpr> A,
                                      std::unique_ptr<VExpr> B) {
  if (!A)
    return B;
  if (!B)
    return A;
  SourceLocation Loc = A->Loc;
  return std::make_unique<VBinOpExpr>(VBinOp::And, std::move(A), std::move(B),
                                      VType::makeBool(), Loc);
}

static std::unique_ptr<VExpr> makeOr(std::unique_ptr<VExpr> A,
                                     std::unique_ptr<VExpr> B) {
  if (!A)
    return B;
  if (!B)
    return A;
  SourceLocation Loc = A->Loc;
  return std::make_unique<VBinOpExpr>(VBinOp::Or, std::move(A), std::move(B),
                                      VType::makeBool(), Loc);
}

static std::unique_ptr<VExpr> cloneForVC(const VExpr *E) {
  return cloneVExpr(E);
}

static std::unique_ptr<VExpr> substResult(std::unique_ptr<VExpr> E,
                                          const std::string &ResultName) {
  if (!E)
    return nullptr;
  if (E->K == VExpr::Result)
    return std::make_unique<VVarExpr>(ResultName, E->Ty, E->Loc);
  if (E->K == VExpr::BinOp) {
    auto *B = static_cast<VBinOpExpr *>(E.get());
    return std::make_unique<VBinOpExpr>(
        B->Op, substResult(cloneForVC(B->Lhs.get()), ResultName),
        substResult(cloneForVC(B->Rhs.get()), ResultName), B->Ty, B->Loc);
  }
  if (E->K == VExpr::UnaryOp) {
    auto *U = static_cast<VUnaryOpExpr *>(E.get());
    return std::make_unique<VUnaryOpExpr>(
        U->Op, substResult(cloneForVC(U->Operand.get()), ResultName), U->Ty,
        U->Loc);
  }
  if (E->K == VExpr::Conditional) {
    auto *C = static_cast<VConditionalExpr *>(E.get());
    return std::make_unique<VConditionalExpr>(
        substResult(cloneForVC(C->Cond.get()), ResultName),
        substResult(cloneForVC(C->Then.get()), ResultName),
        substResult(cloneForVC(C->Else.get()), ResultName), C->Ty, C->Loc);
  }
  return cloneForVC(E.get());
}

static std::unique_ptr<VExpr> makeNot(std::unique_ptr<VExpr> E) {
  SourceLocation Loc = E->Loc;
  return std::make_unique<VUnaryOpExpr>(VUnaryOp::Not, std::move(E),
                                        VType::makeBool(), Loc);
}

std::unique_ptr<VExpr> WPCalculator::computeVC(const PassiveProgram &P) {
  std::string ResultName =
      P.ResultVarName.empty() ? "__result_0" : P.ResultVarName;

  std::unique_ptr<VExpr> WP = makeTrue(SourceLocation());
  for (const auto &Pst : P.ExitAsserts)
    WP = makeAnd(std::move(WP), substResult(cloneForVC(Pst.get()), ResultName));

  for (auto It = P.Stmts.rbegin(); It != P.Stmts.rend(); ++It) {
    const PassiveStmt &S = **It;
    if (!S.Cond)
      continue;
    auto Cond = substResult(cloneForVC(S.Cond.get()), ResultName);
    if (S.K == PassiveStmt::Assume)
      WP = makeOr(makeNot(std::move(Cond)), std::move(WP));
    else
      WP = makeAnd(std::move(Cond), std::move(WP));
  }

  for (auto It = P.EntryAssumes.rbegin(); It != P.EntryAssumes.rend(); ++It) {
    auto Cond = substResult(cloneForVC(It->get()), ResultName);
    WP = makeOr(makeNot(std::move(Cond)), std::move(WP));
  }

  return makeNot(std::move(WP));
}