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

static std::unique_ptr<VExpr> cloneForVC(const VExpr *E) {
  if (!E)
    return nullptr;
  switch (E->K) {
  case VExpr::Literal: {
    const auto *L = static_cast<const VLiteralExpr *>(E);
    return std::make_unique<VLiteralExpr>(L->Value, L->Ty, L->Loc);
  }
  case VExpr::Var: {
    const auto *V = static_cast<const VVarExpr *>(E);
    return std::make_unique<VVarExpr>(V->Name, V->Ty, V->Loc);
  }
  case VExpr::BinOp: {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    return std::make_unique<VBinOpExpr>(
        B->Op, cloneForVC(B->Lhs.get()), cloneForVC(B->Rhs.get()), B->Ty, B->Loc);
  }
  case VExpr::UnaryOp: {
    const auto *U = static_cast<const VUnaryOpExpr *>(E);
    return std::make_unique<VUnaryOpExpr>(
        U->Op, cloneForVC(U->Operand.get()), U->Ty, U->Loc);
  }
  case VExpr::Result: {
    const auto *R = static_cast<const VResultExpr *>(E);
    return std::make_unique<VResultExpr>(R->Ty, R->Loc);
  }
  case VExpr::Old: {
    const auto *O = static_cast<const VOldExpr *>(E);
    return std::make_unique<VOldExpr>(cloneForVC(O->Inner.get()), O->Ty, O->Loc);
  }
  case VExpr::Conditional: {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    return std::make_unique<VConditionalExpr>(
        cloneForVC(C->Cond.get()), cloneForVC(C->Then.get()),
        cloneForVC(C->Else.get()), C->Ty, C->Loc);
  }
  default:
    return nullptr;
  }
}

static std::unique_ptr<VExpr>
substResult(std::unique_ptr<VExpr> E, const std::string &ResultName) {
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

  std::unique_ptr<VExpr> Hyp = makeTrue(SourceLocation());
  for (const auto &A : P.EntryAssumes)
    Hyp = makeAnd(std::move(Hyp), substResult(cloneForVC(A.get()), ResultName));
  for (const auto &S : P.Stmts) {
    if (S->K == PassiveStmt::Assume && S->Cond)
      Hyp = makeAnd(std::move(Hyp),
                    substResult(cloneForVC(S->Cond.get()), ResultName));
  }

  std::unique_ptr<VExpr> Post = makeTrue(SourceLocation());
  for (const auto &Pst : P.ExitAsserts)
    Post = makeAnd(std::move(Post),
                   substResult(cloneForVC(Pst.get()), ResultName));

  // Validity: Hyp => Post  <=>  Hyp /\ !Post is unsat
  return makeAnd(std::move(Hyp), makeNot(std::move(Post)));
}