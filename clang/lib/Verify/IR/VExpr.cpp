//===--- VExpr.cpp --------------------------------------------------------===//
#include "VExpr.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Type.h"

using namespace clang;
using namespace verify;

VType VType::fromQualType(QualType QT, VIntMode DefaultMode,
                          const ASTContext &Ctx) {
  QT = QT.getCanonicalType();
  if (QT->isBooleanType())
    return VType::makeBool();
  if (QT->isVoidType())
    return VType::makeVoid();
  if (QT->isPointerType() || QT->isReferenceType())
    return VType::makePtr();
  if (QT->isIntegerType())
    return VType::makeInt(DefaultMode, Ctx.getIntWidth(QT),
                          QT->isSignedIntegerType());
  if (const auto *ET = QT->getAs<EnumType>()) {
    QualType Underlying = ET->getDecl()->getIntegerType();
    if (!Underlying.isNull())
      return VType::makeInt(DefaultMode, Ctx.getIntWidth(Underlying),
                            Underlying->isSignedIntegerType());
  }
  if (QT->isRecordType())
    return VType::makeStruct();
  return VType::makeUnsupported();
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
    return std::make_unique<VBinOpExpr>(B->Op, cloneVExpr(B->Lhs.get()),
                                        cloneVExpr(B->Rhs.get()), B->Ty,
                                        B->Loc);
  }
  case VExpr::UnaryOp: {
    const auto *U = static_cast<const VUnaryOpExpr *>(E);
    return std::make_unique<VUnaryOpExpr>(U->Op, cloneVExpr(U->Operand.get()),
                                          U->Ty, U->Loc);
  }
  case VExpr::Cast: {
    const auto *C = static_cast<const VCastExpr *>(E);
    return std::make_unique<VCastExpr>(cloneVExpr(C->Inner.get()), C->FromTy,
                                       C->Ty, C->Loc);
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
    return std::make_unique<VOldExpr>(cloneVExpr(O->Inner.get()), O->Ty,
                                      O->Loc);
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
        cloneVExpr(Q->Body.get()), Q->Loc, Q->BinderType);
  }
  case VExpr::Exists: {
    const auto *Q = static_cast<const VQuantifiedExpr *>(E);
    return std::make_unique<VExistsExpr>(
        Q->Binder, cloneVExpr(Q->Lo.get()), cloneVExpr(Q->Hi.get()),
        cloneVExpr(Q->Body.get()), Q->Loc, Q->BinderType);
  }
  case VExpr::HeapStore: {
    const auto *H = static_cast<const VHeapStoreExpr *>(E);
    return std::make_unique<VHeapStoreExpr>(H->HeapBefore, H->HeapAfter,
                                            cloneVExpr(H->Ptr.get()),
                                            cloneVExpr(H->Val.get()), H->Loc);
  }
  case VExpr::FieldAccess: {
    const auto *F = static_cast<const VFieldAccessExpr *>(E);
    return std::make_unique<VFieldAccessExpr>(cloneVExpr(F->Base.get()),
                                              F->Field, F->Ty, F->Loc);
  }
  case VExpr::SpecCall: {
    const auto *C = static_cast<const VSpecCallExpr *>(E);
    std::vector<std::unique_ptr<VExpr>> Args;
    for (const auto &A : C->Args)
      Args.push_back(cloneVExpr(A.get()));
    return std::make_unique<VSpecCallExpr>(C->Callee, C->CalleeIdentity,
                                           std::move(Args), C->Ty, C->Loc);
  }
  case VExpr::OverflowCheck: {
    const auto *O = static_cast<const VOverflowCheckExpr *>(E);
    return std::make_unique<VOverflowCheckExpr>(
        O->Op, cloneVExpr(O->Lhs.get()), cloneVExpr(O->Rhs.get()), O->Loc);
  }
  }
  return nullptr;
}

std::unique_ptr<VExpr>
verify::substituteBinderInVExpr(const VExpr *E, const std::string &Binder,
                                int64_t Value, VIntMode Mode) {
  if (!E)
    return nullptr;
  switch (E->K) {
  case VExpr::Var: {
    const auto *V = static_cast<const VVarExpr *>(E);
    if (V->Name == Binder)
      return std::make_unique<VLiteralExpr>(Value, VType::makeInt32(Mode),
                                            V->Loc);
    return cloneVExpr(E);
  }
  case VExpr::BinOp: {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    return std::make_unique<VBinOpExpr>(
        B->Op, substituteBinderInVExpr(B->Lhs.get(), Binder, Value, Mode),
        substituteBinderInVExpr(B->Rhs.get(), Binder, Value, Mode), B->Ty,
        B->Loc);
  }
  case VExpr::UnaryOp: {
    const auto *U = static_cast<const VUnaryOpExpr *>(E);
    return std::make_unique<VUnaryOpExpr>(
        U->Op, substituteBinderInVExpr(U->Operand.get(), Binder, Value, Mode),
        U->Ty, U->Loc);
  }
  case VExpr::Cast: {
    const auto *C = static_cast<const VCastExpr *>(E);
    return std::make_unique<VCastExpr>(
        substituteBinderInVExpr(C->Inner.get(), Binder, Value, Mode), C->FromTy,
        C->Ty, C->Loc);
  }
  case VExpr::Conditional: {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    return std::make_unique<VConditionalExpr>(
        substituteBinderInVExpr(C->Cond.get(), Binder, Value, Mode),
        substituteBinderInVExpr(C->Then.get(), Binder, Value, Mode),
        substituteBinderInVExpr(C->Else.get(), Binder, Value, Mode), C->Ty,
        C->Loc);
  }
  case VExpr::Forall:
  case VExpr::Exists: {
    const auto *Q = static_cast<const VQuantifiedExpr *>(E);
    if (Q->Binder == Binder)
      return cloneVExpr(E);
    if (Q->K == VExpr::Forall)
      return std::make_unique<VForallExpr>(
          Q->Binder, substituteBinderInVExpr(Q->Lo.get(), Binder, Value, Mode),
          substituteBinderInVExpr(Q->Hi.get(), Binder, Value, Mode),
          substituteBinderInVExpr(Q->Body.get(), Binder, Value, Mode), Q->Loc,
          Q->BinderType);
    return std::make_unique<VExistsExpr>(
        Q->Binder, substituteBinderInVExpr(Q->Lo.get(), Binder, Value, Mode),
        substituteBinderInVExpr(Q->Hi.get(), Binder, Value, Mode),
        substituteBinderInVExpr(Q->Body.get(), Binder, Value, Mode), Q->Loc,
        Q->BinderType);
  }
  default:
    return cloneVExpr(E);
  }
}