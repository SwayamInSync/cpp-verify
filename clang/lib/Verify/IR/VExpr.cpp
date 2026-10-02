//===--- VExpr.cpp --------------------------------------------------------===//
#include "VExpr.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/PrettyPrinter.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/Type.h"
#include "llvm/ADT/StringSwitch.h"

using namespace clang;
using namespace verify;

std::string verify::canonicalTypeIdentity(QualType QT, const ASTContext &Ctx) {
  if (QT.isNull())
    return {};
  QualType C = QT.getCanonicalType().getUnqualifiedType();
  if (!C->isRecordType() && !Ctx.getAsConstantArrayType(C))
    return {};
  PrintingPolicy Policy = Ctx.getPrintingPolicy();
  Policy.SuppressTagKeyword = true;
  Policy.FullyQualifiedName = true;
  Policy.PrintAsCanonical = true;
  Policy.AnonymousTagLocations = true;
  return C.getAsString(Policy);
}

std::optional<VTypeKind> VType::collectionKind(QualType QT) {
  const auto *RD = QT.getCanonicalType()->getAsCXXRecordDecl();
  if (!RD || !RD->getIdentifier())
    return std::nullopt;
  const auto *NS = dyn_cast<NamespaceDecl>(RD->getDeclContext());
  if (!NS || !NS->getIdentifier() || !NS->getIdentifier()->isStr("cppverify") ||
      !NS->getDeclContext()->isTranslationUnit())
    return std::nullopt;
  return llvm::StringSwitch<std::optional<VTypeKind>>(RD->getName())
      .Case("seq", VTypeKind::Seq)
      .Case("set", VTypeKind::Set)
      .Case("multiset", VTypeKind::Multiset)
      .Case("map", VTypeKind::Map)
      .Default(std::nullopt);
}

VType VType::fromQualType(QualType QT, VIntMode DefaultMode,
                          const ASTContext &Ctx) {
  QT = QT.getCanonicalType();
  if (std::optional<VTypeKind> Collection = collectionKind(QT))
    return VType::makeCollection(*Collection);
  if (QT->isBooleanType())
    return VType::makeBool();
  if (QT->isVoidType())
    return VType::makeVoid();
  if (QT->isPointerType() || QT->isReferenceType()) {
    QualType Pointee = QT->getPointeeType();
    if (Pointee->isVoidType() || Pointee->isFunctionType() ||
        Pointee->isIncompleteType())
      return VType::makePtr();
    return VType::makePtr(Ctx.getTypeSizeInChars(Pointee).getQuantity());
  }
  if (QT->isIntegerType()) {
    VType Ty = VType::makeInt(DefaultMode, Ctx.getIntWidth(QT),
                              QT->isSignedIntegerType());
    if (const auto *ET = QT->getAs<EnumType>()) {
      const EnumDecl *ED = ET->getDecl()->getDefinition();
      const unsigned Width = Ctx.getIntWidth(QT);
      if (ED && !ED->isFixed() &&
          std::max(ED->getNumNegativeBits(), ED->getNumPositiveBits() + 1) <
              Width) {
        llvm::APInt Max, Min;
        ED->getValueRange(Max, Min);
        Ty.EnumMin = llvm::toString(Min, 10, /*Signed=*/true);
        Ty.EnumMax = llvm::toString(Max, 10, /*Signed=*/true);
      }
    }
    return Ty;
  }
  if (const auto *ET = QT->getAs<EnumType>()) {
    QualType Underlying = ET->getDecl()->getIntegerType();
    if (!Underlying.isNull())
      return VType::makeInt(DefaultMode, Ctx.getIntWidth(Underlying),
                            Underlying->isSignedIntegerType());
  }
  if (const auto *CAT = Ctx.getAsConstantArrayType(QT)) {
    VType Ty = VType::makeArray();
    Ty.TypeIdentity = canonicalTypeIdentity(QT, Ctx);
    if (QT->isIncompleteType() || CAT->getElementType()->isIncompleteType())
      return Ty;
    Ty.ObjectSizeBytes = Ctx.getTypeSizeInChars(QT).getQuantity();
    Ty.ObjectAlignBytes = Ctx.getTypeAlignInChars(QT).getQuantity();
    Ty.ArrayCount = CAT->getSize().getZExtValue();
    Ty.ArrayStrideBytes =
        Ctx.getTypeSizeInChars(CAT->getElementType()).getQuantity();
    return Ty;
  }
  if (QT->isRecordType()) {
    VType Ty = VType::makeStruct();
    if (!QT->isIncompleteType()) {
      Ty.ObjectSizeBytes = Ctx.getTypeSizeInChars(QT).getQuantity();
      Ty.ObjectAlignBytes = Ctx.getTypeAlignInChars(QT).getQuantity();
    }
    Ty.TypeIdentity = canonicalTypeIdentity(QT, Ctx);
    return Ty;
  }
  return VType::makeUnsupported();
}

static std::unique_ptr<VExpr> cloneVExprImpl(const VExpr *E) {
  if (!E)
    return nullptr;
  switch (E->K) {
  case VExpr::Literal: {
    const auto *L = static_cast<const VLiteralExpr *>(E);
    return std::make_unique<VLiteralExpr>(L->Value, L->Ty, L->Loc);
  }
  case VExpr::Var: {
    const auto *V = static_cast<const VVarExpr *>(E);
    return std::make_unique<VVarExpr>(V->Name, V->Ty, V->Loc,
                                      V->ProvenanceVariable);
  }
  case VExpr::BinOp: {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    return std::make_unique<VBinOpExpr>(B->Op, cloneVExpr(B->Lhs.get()),
                                        cloneVExpr(B->Rhs.get()), B->Ty,
                                        B->Loc);
  }
  case VExpr::UnaryOp: {
    const auto *U = static_cast<const VUnaryOpExpr *>(E);
    return std::make_unique<VUnaryOpExpr>(
        U->Op, cloneVExpr(U->Operand.get()), U->Ty, U->Loc,
        U->AllocationHeapVar, U->LivenessHeapVar, U->InitializationHeapVar);
  }
  case VExpr::Cast: {
    const auto *C = static_cast<const VCastExpr *>(E);
    return std::make_unique<VCastExpr>(cloneVExpr(C->Inner.get()), C->FromTy,
                                       C->Ty, C->Loc, C->IsTrigger);
  }
  case VExpr::Load: {
    const auto *L = static_cast<const VLoadExpr *>(E);
    return std::make_unique<VLoadExpr>(cloneVExpr(L->Ptr.get()), L->Ty, L->Loc,
                                       L->HeapVar,
                                       cloneVExpr(L->AccessCondition.get()));
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
  case VExpr::HeapFrame: {
    const auto *H = static_cast<const VHeapFrameExpr *>(E);
    std::vector<std::pair<std::unique_ptr<VExpr>, std::unique_ptr<VExpr>>>
        Regions;
    for (const auto &[Lo, Hi] : H->Regions)
      Regions.emplace_back(cloneVExpr(Lo.get()), cloneVExpr(Hi.get()));
    return std::make_unique<VHeapFrameExpr>(H->HeapBefore, H->HeapAfter,
                                            std::move(Regions), H->Loc);
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
                                           std::move(Args), C->Ty, C->Loc,
                                           C->ReadsHeap, C->HeapVar);
  }
  case VExpr::OverflowCheck: {
    const auto *O = static_cast<const VOverflowCheckExpr *>(E);
    return std::make_unique<VOverflowCheckExpr>(
        O->Op, cloneVExpr(O->Lhs.get()), cloneVExpr(O->Rhs.get()), O->Loc);
  }
  }
  return nullptr;
}

VIntMode verify::evaluatedIntMode(const VExpr *E) {
  if (!E)
    return VIntMode::Machine;
  if (!E->Ty.isInt() || E->Ty.IntMode == VIntMode::Math)
    return E->Ty.IntMode;
  switch (E->K) {
  case VExpr::BinOp: {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    switch (B->Op) {
    case VBinOp::Add:
    case VBinOp::Sub:
    case VBinOp::Mul:
    case VBinOp::Div:
    case VBinOp::Rem:
      if (evaluatedIntMode(B->Lhs.get()) == VIntMode::Math ||
          evaluatedIntMode(B->Rhs.get()) == VIntMode::Math)
        return VIntMode::Math;
      break;
    default:
      break;
    }
    break;
  }
  case VExpr::UnaryOp: {
    const auto *U = static_cast<const VUnaryOpExpr *>(E);
    if (U->Op == VUnaryOp::Neg)
      return evaluatedIntMode(U->Operand.get());
    break;
  }
  case VExpr::Conditional: {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    if (evaluatedIntMode(C->Then.get()) == VIntMode::Math ||
        evaluatedIntMode(C->Else.get()) == VIntMode::Math)
      return VIntMode::Math;
    break;
  }
  default:
    break;
  }
  return E->Ty.IntMode;
}

std::unique_ptr<VExpr> verify::cloneVExpr(const VExpr *E) {
  auto Copy = cloneVExprImpl(E);
  if (Copy && E)
    Copy->EndLoc = E->EndLoc;
  return Copy;
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
        U->Ty, U->Loc, U->AllocationHeapVar, U->LivenessHeapVar,
        U->InitializationHeapVar);
  }
  case VExpr::Cast: {
    const auto *C = static_cast<const VCastExpr *>(E);
    return std::make_unique<VCastExpr>(
        substituteBinderInVExpr(C->Inner.get(), Binder, Value, Mode), C->FromTy,
        C->Ty, C->Loc, C->IsTrigger);
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
void verify::forEachVExprChild(const VExpr *E,
                               llvm::function_ref<void(const VExpr *)> Visit) {
  if (!E)
    return;
  auto visit = [&](const std::unique_ptr<VExpr> &Child) {
    if (Child)
      Visit(Child.get());
  };
  switch (E->K) {
  case VExpr::Literal:
  case VExpr::Var:
  case VExpr::Result:
    return;
  case VExpr::BinOp: {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    visit(B->Lhs);
    visit(B->Rhs);
    return;
  }
  case VExpr::UnaryOp:
    visit(static_cast<const VUnaryOpExpr *>(E)->Operand);
    return;
  case VExpr::Cast:
    visit(static_cast<const VCastExpr *>(E)->Inner);
    return;
  case VExpr::Load: {
    const auto *L = static_cast<const VLoadExpr *>(E);
    visit(L->Ptr);
    visit(L->AccessCondition);
    return;
  }
  case VExpr::Old:
    visit(static_cast<const VOldExpr *>(E)->Inner);
    return;
  case VExpr::Conditional: {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    visit(C->Cond);
    visit(C->Then);
    visit(C->Else);
    return;
  }
  case VExpr::Forall:
  case VExpr::Exists: {
    const auto *Q = static_cast<const VQuantifiedExpr *>(E);
    visit(Q->Lo);
    visit(Q->Hi);
    visit(Q->Body);
    return;
  }
  case VExpr::HeapStore: {
    const auto *H = static_cast<const VHeapStoreExpr *>(E);
    visit(H->Ptr);
    visit(H->Val);
    return;
  }
  case VExpr::HeapFrame:
    for (const auto &[Lo, Hi] : static_cast<const VHeapFrameExpr *>(E)->Regions) {
      visit(Lo);
      visit(Hi);
    }
    return;
  case VExpr::FieldAccess:
    visit(static_cast<const VFieldAccessExpr *>(E)->Base);
    return;
  case VExpr::SpecCall:
    for (const auto &Arg : static_cast<const VSpecCallExpr *>(E)->Args)
      visit(Arg);
    return;
  case VExpr::OverflowCheck: {
    const auto *O = static_cast<const VOverflowCheckExpr *>(E);
    visit(O->Lhs);
    visit(O->Rhs);
    return;
  }
  }
}

void verify::forEachVExprChildSlot(
    VExpr *E, llvm::function_ref<void(std::unique_ptr<VExpr> &)> Visit) {
  if (!E)
    return;
  auto visit = [&](std::unique_ptr<VExpr> &Child) {
    if (Child)
      Visit(Child);
  };
  switch (E->K) {
  case VExpr::Literal:
  case VExpr::Var:
  case VExpr::Result:
    return;
  case VExpr::BinOp: {
    auto *B = static_cast<VBinOpExpr *>(E);
    visit(B->Lhs);
    visit(B->Rhs);
    return;
  }
  case VExpr::UnaryOp:
    visit(static_cast<VUnaryOpExpr *>(E)->Operand);
    return;
  case VExpr::Cast:
    visit(static_cast<VCastExpr *>(E)->Inner);
    return;
  case VExpr::Load: {
    auto *L = static_cast<VLoadExpr *>(E);
    visit(L->Ptr);
    visit(L->AccessCondition);
    return;
  }
  case VExpr::Old:
    visit(static_cast<VOldExpr *>(E)->Inner);
    return;
  case VExpr::Conditional: {
    auto *C = static_cast<VConditionalExpr *>(E);
    visit(C->Cond);
    visit(C->Then);
    visit(C->Else);
    return;
  }
  case VExpr::Forall:
  case VExpr::Exists: {
    auto *Q = static_cast<VQuantifiedExpr *>(E);
    visit(Q->Lo);
    visit(Q->Hi);
    visit(Q->Body);
    return;
  }
  case VExpr::HeapStore: {
    auto *H = static_cast<VHeapStoreExpr *>(E);
    visit(H->Ptr);
    visit(H->Val);
    return;
  }
  case VExpr::HeapFrame:
    for (auto &[Lo, Hi] : static_cast<VHeapFrameExpr *>(E)->Regions) {
      visit(Lo);
      visit(Hi);
    }
    return;
  case VExpr::FieldAccess:
    visit(static_cast<VFieldAccessExpr *>(E)->Base);
    return;
  case VExpr::SpecCall:
    for (auto &Arg : static_cast<VSpecCallExpr *>(E)->Args)
      visit(Arg);
    return;
  case VExpr::OverflowCheck: {
    auto *O = static_cast<VOverflowCheckExpr *>(E);
    visit(O->Lhs);
    visit(O->Rhs);
    return;
  }
  }
}
