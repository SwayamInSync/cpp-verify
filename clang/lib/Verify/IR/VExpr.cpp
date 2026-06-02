//===--- VExpr.cpp --------------------------------------------------------===//
#include "VExpr.h"
#include "clang/AST/Type.h"

using namespace clang;
using namespace verify;

VType VType::fromQualType(QualType QT, VIntMode DefaultMode) {
  QT = QT.getCanonicalType();
  if (QT->isBooleanType())
    return VType::makeBool();
  if (QT->isVoidType())
    return VType::makeVoid();
  if (QT->isPointerType() || QT->isReferenceType())
    return VType::makePtr();
  if (QT->isIntegerType())
    return VType::makeInt32(DefaultMode);
  return VType::makeInt32(DefaultMode);
}

std::unique_ptr<VExpr> verify::cloneVExpr(const VExpr *E) {
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
        B->Op, cloneVExpr(B->Lhs.get()), cloneVExpr(B->Rhs.get()), B->Ty, B->Loc);
  }
  case VExpr::UnaryOp: {
    const auto *U = static_cast<const VUnaryOpExpr *>(E);
    return std::make_unique<VUnaryOpExpr>(
        U->Op, cloneVExpr(U->Operand.get()), U->Ty, U->Loc);
  }
  case VExpr::Cast: {
    const auto *C = static_cast<const VCastExpr *>(E);
    return std::make_unique<VCastExpr>(cloneVExpr(C->Inner.get()), C->FromTy, C->Ty,
                                       C->Loc);
  }
  case VExpr::Load: {
    const auto *L = static_cast<const VLoadExpr *>(E);
    return std::make_unique<VLoadExpr>(cloneVExpr(L->Ptr.get()), L->Ty, L->Loc,
                                       L->HeapVar);
  }
  case VExpr::Result:
    return std::make_unique<VResultExpr>(E->Ty, E->Loc);
  case VExpr::Old: {
    const auto *O = static_cast<const VOldExpr *>(E);
    return std::make_unique<VOldExpr>(cloneVExpr(O->Inner.get()), O->Ty, O->Loc);
  }
  case VExpr::Conditional: {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    return std::make_unique<VConditionalExpr>(
        cloneVExpr(C->Cond.get()), cloneVExpr(C->Then.get()),
        cloneVExpr(C->Else.get()), C->Ty, C->Loc);
  }
  case VExpr::Forall: {
    const auto *Q = static_cast<const VQuantifiedExpr *>(E);
    return std::make_unique<VForallExpr>(
        Q->Binder, cloneVExpr(Q->Lo.get()), cloneVExpr(Q->Hi.get()),
        cloneVExpr(Q->Body.get()), Q->Loc);
  }
  case VExpr::Exists: {
    const auto *Q = static_cast<const VQuantifiedExpr *>(E);
    return std::make_unique<VExistsExpr>(
        Q->Binder, cloneVExpr(Q->Lo.get()), cloneVExpr(Q->Hi.get()),
        cloneVExpr(Q->Body.get()), Q->Loc);
  }
  case VExpr::HeapStore: {
    const auto *H = static_cast<const VHeapStoreExpr *>(E);
    return std::make_unique<VHeapStoreExpr>(
        H->HeapBefore, H->HeapAfter, cloneVExpr(H->Ptr.get()),
        cloneVExpr(H->Val.get()), H->Loc);
  }
  }
  return nullptr;
}