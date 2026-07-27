//===--- Passivize.cpp ----------------------------------------------------===//
#include "Passivize.h"
#include "SpecInline.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/SmallString.h"
#include <limits>
#include <map>
#include <set>
#include <string>

using namespace clang;
using namespace verify;

struct CloneCtx {
  const std::map<std::string, std::string> &Renames;
  const std::map<std::string, std::unique_ptr<VExpr>> &OldState;
  bool UseOldState = false;
  std::set<std::string> BoundVars;
};

static std::unique_ptr<VExpr> cloneExpr(const VExpr *E, const CloneCtx &Ctx);

static std::string stateHeapName(const CloneCtx &Ctx, const char *Base,
                                 const std::string &Explicit) {
  if (!Explicit.empty())
    return Explicit;
  if (Ctx.UseOldState)
    if (auto It = Ctx.OldState.find(Base); It != Ctx.OldState.end())
      if (It->second->K == VExpr::Var)
        return static_cast<const VVarExpr *>(It->second.get())->Name;
  if (auto It = Ctx.Renames.find(Base); It != Ctx.Renames.end())
    return It->second;
  return std::string(Base) + "_0";
}

static std::string stateVariableName(const CloneCtx &Ctx,
                                     const std::string &Name) {
  if (Name.empty())
    return "";
  if (Ctx.UseOldState)
    if (auto It = Ctx.OldState.find(Name); It != Ctx.OldState.end())
      if (It->second->K == VExpr::Var)
        return static_cast<const VVarExpr *>(It->second.get())->Name;
  if (auto It = Ctx.Renames.find(Name); It != Ctx.Renames.end())
    return It->second;
  return Name;
}

static std::unique_ptr<VExpr> cloneExpr(const VExpr *E, const CloneCtx &Ctx) {
  if (!E)
    return nullptr;
  if (Ctx.UseOldState && E->K == VExpr::Old) {
    const auto *O = static_cast<const VOldExpr *>(E);
    CloneCtx Inner = Ctx;
    Inner.UseOldState = true;
    return cloneExpr(O->Inner.get(), Inner);
  }
  switch (E->K) {
  case VExpr::Literal: {
    const auto *L = static_cast<const VLiteralExpr *>(E);
    return std::make_unique<VLiteralExpr>(L->Value, L->Ty, L->Loc);
  }
  case VExpr::Var: {
    const auto *V = static_cast<const VVarExpr *>(E);
    std::string Name = V->Name;
    if (Ctx.BoundVars.count(Name))
      return std::make_unique<VVarExpr>(Name, V->Ty, V->Loc,
                                        V->ProvenanceVariable);
    if (Ctx.UseOldState) {
      if (auto It = Ctx.OldState.find(Name); It != Ctx.OldState.end())
        return cloneExpr(It->second.get(), CloneCtx{Ctx.Renames, Ctx.OldState,
                                                    false, Ctx.BoundVars});
    }
    if (auto It = Ctx.Renames.find(Name); It != Ctx.Renames.end())
      Name = It->second;
    return std::make_unique<VVarExpr>(
        Name, V->Ty, V->Loc, stateVariableName(Ctx, V->ProvenanceVariable));
  }
  case VExpr::BinOp: {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    return std::make_unique<VBinOpExpr>(B->Op, cloneExpr(B->Lhs.get(), Ctx),
                                        cloneExpr(B->Rhs.get(), Ctx), B->Ty,
                                        B->Loc);
  }
  case VExpr::UnaryOp: {
    const auto *U = static_cast<const VUnaryOpExpr *>(E);
    return std::make_unique<VUnaryOpExpr>(
        U->Op, cloneExpr(U->Operand.get(), Ctx), U->Ty, U->Loc,
        stateHeapName(Ctx, VAllocationHeapName, U->AllocationHeapVar),
        stateHeapName(Ctx, VLivenessHeapName, U->LivenessHeapVar),
        stateHeapName(Ctx, VInitializationHeapName, U->InitializationHeapVar));
  }
  case VExpr::Cast: {
    const auto *C = static_cast<const VCastExpr *>(E);
    return std::make_unique<VCastExpr>(cloneExpr(C->Inner.get(), Ctx),
                                       C->FromTy, C->Ty, C->Loc);
  }
  case VExpr::Load: {
    const auto *L = static_cast<const VLoadExpr *>(E);
    std::string Heap = Ctx.Renames.count(VHeapName)
                           ? Ctx.Renames.at(VHeapName)
                           : std::string(VHeapName) + "_0";
    if (Ctx.UseOldState) {
      if (auto HIt = Ctx.OldState.find(VHeapName); HIt != Ctx.OldState.end()) {
        if (const auto *HV = static_cast<const VVarExpr *>(HIt->second.get()))
          Heap = HV->Name;
      }
    } else if (!L->HeapVar.empty()) {
      Heap = L->HeapVar;
    }
    return std::make_unique<VLoadExpr>(cloneExpr(L->Ptr.get(), Ctx), L->Ty,
                                       L->Loc, Heap);
  }
  case VExpr::Result: {
    if (auto It = Ctx.Renames.find("result"); It != Ctx.Renames.end())
      return std::make_unique<VVarExpr>(It->second, E->Ty, E->Loc);
    return std::make_unique<VResultExpr>(E->Ty, E->Loc);
  }
  case VExpr::Old: {
    const auto *O = static_cast<const VOldExpr *>(E);
    CloneCtx Inner = Ctx;
    Inner.UseOldState = true;
    return cloneExpr(O->Inner.get(), Inner);
  }
  case VExpr::Conditional: {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    return std::make_unique<VConditionalExpr>(
        cloneExpr(C->Cond.get(), Ctx), cloneExpr(C->Then.get(), Ctx),
        cloneExpr(C->Else.get(), Ctx), C->Ty, C->Loc);
  }
  case VExpr::FieldAccess: {
    const auto *F = static_cast<const VFieldAccessExpr *>(E);
    std::string Name;
    if (F->Base->K == VExpr::Var)
      Name = static_cast<const VVarExpr *>(F->Base.get())->Name;
    else if (F->Base->K == VExpr::Result) {
      if (auto It = Ctx.Renames.find("result"); It != Ctx.Renames.end())
        Name = It->second;
      else
        Name = "result";
    } else
      return std::make_unique<VVarExpr>("__cppverify_unsupported_field_base",
                                        VType::makeUnsupported(), F->Loc);
    Name += "." + F->Field;
    if (Ctx.UseOldState) {
      if (auto It = Ctx.OldState.find(Name); It != Ctx.OldState.end())
        return cloneExpr(It->second.get(), CloneCtx{Ctx.Renames, Ctx.OldState,
                                                    false, Ctx.BoundVars});
    }
    if (auto It = Ctx.Renames.find(Name); It != Ctx.Renames.end())
      Name = It->second;
    return std::make_unique<VVarExpr>(Name, F->Ty, F->Loc);
  }
  case VExpr::SpecCall: {
    const auto *C = static_cast<const VSpecCallExpr *>(E);
    std::vector<std::unique_ptr<VExpr>> Args;
    for (const auto &A : C->Args)
      Args.push_back(cloneExpr(A.get(), Ctx));
    return std::make_unique<VSpecCallExpr>(C->Callee, C->CalleeIdentity,
                                           std::move(Args), C->Ty, C->Loc);
  }
  case VExpr::OverflowCheck: {
    const auto *O = static_cast<const VOverflowCheckExpr *>(E);
    return std::make_unique<VOverflowCheckExpr>(
        O->Op, cloneExpr(O->Lhs.get(), Ctx),
        O->Rhs ? cloneExpr(O->Rhs.get(), Ctx) : nullptr, O->Loc);
  }
  case VExpr::Forall:
  case VExpr::Exists: {
    const auto *Q = static_cast<const VQuantifiedExpr *>(E);
    CloneCtx BodyCtx = Ctx;
    BodyCtx.BoundVars.insert(Q->Binder);
    auto Body = cloneExpr(Q->Body.get(), BodyCtx);
    return E->K == VExpr::Forall
               ? std::unique_ptr<VExpr>(std::make_unique<VForallExpr>(
                     Q->Binder, cloneExpr(Q->Lo.get(), Ctx),
                     cloneExpr(Q->Hi.get(), Ctx), std::move(Body), Q->Loc,
                     Q->BinderType))
               : std::unique_ptr<VExpr>(std::make_unique<VExistsExpr>(
                     Q->Binder, cloneExpr(Q->Lo.get(), Ctx),
                     cloneExpr(Q->Hi.get(), Ctx), std::move(Body), Q->Loc,
                     Q->BinderType));
  }
  case VExpr::HeapStore: {
    const auto *H = static_cast<const VHeapStoreExpr *>(E);
    return std::make_unique<VHeapStoreExpr>(
        H->HeapBefore, H->HeapAfter, cloneExpr(H->Ptr.get(), Ctx),
        cloneExpr(H->Val.get(), Ctx), H->Loc);
  }
  }
  return nullptr;
}

static std::unique_ptr<VExpr>
makeEq(std::unique_ptr<VExpr> L, std::unique_ptr<VExpr> R, SourceLocation Loc) {
  return std::make_unique<VBinOpExpr>(VBinOp::Eq, std::move(L), std::move(R),
                                      VType::makeBool(), Loc);
}

static std::unique_ptr<VExpr> makeNot(std::unique_ptr<VExpr> E,
                                      SourceLocation Loc) {
  return std::make_unique<VUnaryOpExpr>(VUnaryOp::Not, std::move(E),
                                        VType::makeBool(), Loc);
}

static std::unique_ptr<VExpr> makeAnd(std::unique_ptr<VExpr> L,
                                      std::unique_ptr<VExpr> R,
                                      SourceLocation Loc) {
  return std::make_unique<VBinOpExpr>(VBinOp::And, std::move(L), std::move(R),
                                      VType::makeBool(), Loc);
}

static std::unique_ptr<VExpr>
makeOr(std::unique_ptr<VExpr> L, std::unique_ptr<VExpr> R, SourceLocation Loc) {
  return std::make_unique<VBinOpExpr>(VBinOp::Or, std::move(L), std::move(R),
                                      VType::makeBool(), Loc);
}

static std::unique_ptr<VExpr> makeBoolLiteral(bool Value, SourceLocation Loc) {
  return std::make_unique<VLiteralExpr>(Value, VType::makeBool(), Loc);
}

static std::unique_ptr<VExpr>
buildTupleNonNegative(const std::vector<std::unique_ptr<VExpr>> &Values,
                      SourceLocation Loc) {
  std::unique_ptr<VExpr> Result = makeBoolLiteral(true, Loc);
  for (const auto &Value : Values) {
    if (!Value)
      return makeBoolLiteral(false, Loc);
    auto NonNegative = std::make_unique<VBinOpExpr>(
        VBinOp::Ge, cloneVExpr(Value.get()),
        std::make_unique<VLiteralExpr>(0, Value->Ty, Loc), VType::makeBool(),
        Loc);
    Result = makeAnd(std::move(Result), std::move(NonNegative), Loc);
  }
  return Result;
}

static std::unique_ptr<VExpr>
buildLexDecrease(const std::vector<std::unique_ptr<VExpr>> &NewValues,
                 const std::vector<std::unique_ptr<VExpr>> &OldValues,
                 SourceLocation Loc) {
  if (NewValues.empty() || NewValues.size() != OldValues.size())
    return makeBoolLiteral(false, Loc);

  std::unique_ptr<VExpr> LexLess = makeBoolLiteral(false, Loc);
  for (size_t J = 0; J < NewValues.size(); ++J) {
    std::unique_ptr<VExpr> Disjunct = std::make_unique<VBinOpExpr>(
        VBinOp::Lt, cloneVExpr(NewValues[J].get()),
        cloneVExpr(OldValues[J].get()), VType::makeBool(), Loc);
    for (size_t I = 0; I < J; ++I)
      Disjunct =
          makeAnd(std::make_unique<VBinOpExpr>(
                      VBinOp::Eq, cloneVExpr(NewValues[I].get()),
                      cloneVExpr(OldValues[I].get()), VType::makeBool(), Loc),
                  std::move(Disjunct), Loc);
    LexLess = makeOr(std::move(LexLess), std::move(Disjunct), Loc);
  }
  return makeAnd(std::move(LexLess), buildTupleNonNegative(NewValues, Loc),
                 Loc);
}

static std::unique_ptr<VExpr> makeImplies(std::unique_ptr<VExpr> L,
                                          std::unique_ptr<VExpr> R,
                                          SourceLocation Loc) {
  return std::make_unique<VBinOpExpr>(VBinOp::Or, makeNot(std::move(L), Loc),
                                      std::move(R), VType::makeBool(), Loc);
}

static std::unique_ptr<VExpr> safetyForExpr(const VExpr *E,
                                            const FunctionMap *FnMap);

static std::unique_ptr<VExpr> combineSafety(std::unique_ptr<VExpr> L,
                                            std::unique_ptr<VExpr> R,
                                            SourceLocation Loc) {
  return makeAnd(std::move(L), std::move(R), Loc);
}

static bool isIntegerType(const VType &Ty) {
  return Ty.Kind == VTypeKind::Int32 || Ty.Kind == VTypeKind::Int64;
}

static bool isSignedMachineInteger(const VType &Ty) {
  return isIntegerType(Ty) && Ty.IntMode == VIntMode::Machine && Ty.IsSigned;
}

static std::string signedLimit(unsigned BitWidth, bool Minimum) {
  llvm::APInt Value = Minimum ? llvm::APInt::getSignedMinValue(BitWidth)
                              : llvm::APInt::getSignedMaxValue(BitWidth);
  llvm::SmallString<64> Buffer;
  Value.toString(Buffer, 10, true);
  return std::string(Buffer);
}

static std::string unsignedMaximum(unsigned BitWidth) {
  llvm::APInt Value = llvm::APInt::getMaxValue(BitWidth);
  llvm::SmallString<64> Buffer;
  Value.toString(Buffer, 10, false);
  return std::string(Buffer);
}

static std::unique_ptr<VExpr> mathCast(const VExpr *E) {
  VType MathTy = E->Ty;
  MathTy.IntMode = VIntMode::Math;
  return std::make_unique<VCastExpr>(cloneVExpr(E), E->Ty, MathTy, E->Loc);
}

static std::unique_ptr<VExpr> signedArithmeticSafety(const VBinOpExpr *B) {
  const VType &Ty = B->Lhs->Ty;
  if (!isSignedMachineInteger(Ty))
    return makeBoolLiteral(true, B->Loc);
  if (Ty.BitWidth == 0 ||
      Ty.BitWidth > std::numeric_limits<unsigned>::max() / 2)
    return makeBoolLiteral(false, B->Loc);

  VType WideTy = VType::makeInt(VIntMode::Machine, Ty.BitWidth * 2, true);
  auto WideLhs =
      std::make_unique<VCastExpr>(cloneVExpr(B->Lhs.get()), Ty, WideTy, B->Loc);
  auto WideRhs = std::make_unique<VCastExpr>(cloneVExpr(B->Rhs.get()),
                                             B->Rhs->Ty, WideTy, B->Loc);
  auto Value = std::make_unique<VBinOpExpr>(B->Op, std::move(WideLhs),
                                            std::move(WideRhs), WideTy, B->Loc);
  auto Lower = std::make_unique<VBinOpExpr>(
      VBinOp::Ge, cloneVExpr(Value.get()),
      std::make_unique<VLiteralExpr>(signedLimit(Ty.BitWidth, true), WideTy,
                                     B->Loc),
      VType::makeBool(), B->Loc);
  auto Upper = std::make_unique<VBinOpExpr>(
      VBinOp::Le, std::move(Value),
      std::make_unique<VLiteralExpr>(signedLimit(Ty.BitWidth, false), WideTy,
                                     B->Loc),
      VType::makeBool(), B->Loc);
  return makeAnd(std::move(Lower), std::move(Upper), B->Loc);
}

static std::unique_ptr<VExpr> shiftSafety(const VBinOpExpr *B) {
  const unsigned BitWidth = B->Lhs->Ty.BitWidth;
  if (BitWidth == 0)
    return makeBoolLiteral(false, B->Loc);

  auto NonNegative = std::make_unique<VBinOpExpr>(
      VBinOp::Ge, cloneVExpr(B->Rhs.get()),
      std::make_unique<VLiteralExpr>(0, B->Rhs->Ty, B->Loc), VType::makeBool(),
      B->Loc);
  auto BelowWidth = std::make_unique<VBinOpExpr>(
      VBinOp::Lt, cloneVExpr(B->Rhs.get()),
      std::make_unique<VLiteralExpr>(BitWidth, B->Rhs->Ty, B->Loc),
      VType::makeBool(), B->Loc);
  auto Safe = makeAnd(std::move(NonNegative), std::move(BelowWidth), B->Loc);

  if (B->Op != VBinOp::Shl || !isSignedMachineInteger(B->Lhs->Ty))
    return Safe;

  auto NonNegativeLhs = std::make_unique<VBinOpExpr>(
      VBinOp::Ge, cloneVExpr(B->Lhs.get()),
      std::make_unique<VLiteralExpr>(0, B->Lhs->Ty, B->Loc), VType::makeBool(),
      B->Loc);
  VType UnsignedTy = B->Lhs->Ty;
  UnsignedTy.IsSigned = false;
  auto UnsignedLhs = std::make_unique<VCastExpr>(
      cloneVExpr(B->Lhs.get()), B->Lhs->Ty, UnsignedTy, B->Loc);
  auto ShiftedMax = std::make_unique<VBinOpExpr>(
      VBinOp::Shr,
      std::make_unique<VLiteralExpr>(unsignedMaximum(BitWidth), UnsignedTy,
                                     B->Loc),
      cloneVExpr(B->Rhs.get()), UnsignedTy, B->Loc);
  auto Representable = std::make_unique<VBinOpExpr>(
      VBinOp::Le, std::move(UnsignedLhs), std::move(ShiftedMax),
      VType::makeBool(), B->Loc);
  Safe = combineSafety(std::move(Safe), std::move(NonNegativeLhs), B->Loc);
  return combineSafety(std::move(Safe), std::move(Representable), B->Loc);
}

static const VExpr *pointerBase(const VExpr *E) {
  while (E && E->K == VExpr::Cast)
    E = static_cast<const VCastExpr *>(E)->Inner.get();
  if (E && E->K == VExpr::BinOp) {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    if ((B->Op == VBinOp::Add || B->Op == VBinOp::Sub) &&
        B->Lhs->Ty.Kind == VTypeKind::Ptr)
      return pointerBase(B->Lhs.get());
  }
  return E;
}

static std::unique_ptr<VExpr> pointerProvenance(const VExpr *E) {
  const VExpr *Base = pointerBase(E);
  if (!Base || Base->K != VExpr::Var)
    return nullptr;
  const auto *V = static_cast<const VVarExpr *>(Base);
  if (V->ProvenanceVariable.empty())
    return nullptr;
  return std::make_unique<VVarExpr>(V->ProvenanceVariable, VType::makePtr(),
                                    V->Loc);
}

static bool hasPointerProvenance(const VExpr *E) {
  return pointerProvenance(E) != nullptr;
}

static bool referencesVar(const VExpr *E, const std::string &Name) {
  if (!E)
    return false;
  switch (E->K) {
  case VExpr::Literal:
  case VExpr::Result:
    return false;
  case VExpr::Var:
    return static_cast<const VVarExpr *>(E)->Name == Name;
  case VExpr::BinOp: {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    return referencesVar(B->Lhs.get(), Name) ||
           referencesVar(B->Rhs.get(), Name);
  }
  case VExpr::UnaryOp:
    return referencesVar(static_cast<const VUnaryOpExpr *>(E)->Operand.get(),
                         Name);
  case VExpr::Cast:
    return referencesVar(static_cast<const VCastExpr *>(E)->Inner.get(), Name);
  case VExpr::Load:
    return referencesVar(static_cast<const VLoadExpr *>(E)->Ptr.get(), Name);
  case VExpr::Old:
    return referencesVar(static_cast<const VOldExpr *>(E)->Inner.get(), Name);
  case VExpr::Conditional: {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    return referencesVar(C->Cond.get(), Name) ||
           referencesVar(C->Then.get(), Name) ||
           referencesVar(C->Else.get(), Name);
  }
  case VExpr::Forall:
  case VExpr::Exists: {
    const auto *Q = static_cast<const VQuantifiedExpr *>(E);
    return referencesVar(Q->Lo.get(), Name) ||
           referencesVar(Q->Hi.get(), Name) ||
           referencesVar(Q->Body.get(), Name);
  }
  case VExpr::HeapStore: {
    const auto *H = static_cast<const VHeapStoreExpr *>(E);
    return referencesVar(H->Ptr.get(), Name) ||
           referencesVar(H->Val.get(), Name);
  }
  case VExpr::FieldAccess:
    return referencesVar(static_cast<const VFieldAccessExpr *>(E)->Base.get(),
                         Name);
  case VExpr::SpecCall:
    for (const auto &Arg : static_cast<const VSpecCallExpr *>(E)->Args)
      if (referencesVar(Arg.get(), Name))
        return true;
    return false;
  case VExpr::OverflowCheck: {
    const auto *O = static_cast<const VOverflowCheckExpr *>(E);
    return referencesVar(O->Lhs.get(), Name) ||
           referencesVar(O->Rhs.get(), Name);
  }
  }
  return false;
}

static bool isDirectPointerParam(const VExpr *E, const std::string &Name) {
  while (E && E->K == VExpr::Cast)
    E = static_cast<const VCastExpr *>(E)->Inner.get();
  return E && E->K == VExpr::Var &&
         static_cast<const VVarExpr *>(E)->Name == Name;
}

static bool scalarDynamicExprSafe(const VExpr *E, const std::string &Param) {
  if (!E)
    return true;
  switch (E->K) {
  case VExpr::Literal:
  case VExpr::Var:
  case VExpr::Result:
    return true;
  case VExpr::BinOp: {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    if ((B->Lhs->Ty.Kind == VTypeKind::Ptr ||
         B->Rhs->Ty.Kind == VTypeKind::Ptr) &&
        referencesVar(B, Param) && B->Op != VBinOp::Eq && B->Op != VBinOp::Ne)
      return false;
    return scalarDynamicExprSafe(B->Lhs.get(), Param) &&
           scalarDynamicExprSafe(B->Rhs.get(), Param);
  }
  case VExpr::UnaryOp:
    return scalarDynamicExprSafe(
        static_cast<const VUnaryOpExpr *>(E)->Operand.get(), Param);
  case VExpr::Cast: {
    const auto *C = static_cast<const VCastExpr *>(E);
    if (C->Inner->Ty.Kind == VTypeKind::Ptr &&
        referencesVar(C->Inner.get(), Param) && C->Ty.Kind != VTypeKind::Ptr &&
        C->Ty.Kind != VTypeKind::Bool)
      return false;
    return scalarDynamicExprSafe(C->Inner.get(), Param);
  }
  case VExpr::Load: {
    const auto *L = static_cast<const VLoadExpr *>(E);
    if (referencesVar(L->Ptr.get(), Param) &&
        !isDirectPointerParam(L->Ptr.get(), Param))
      return false;
    return scalarDynamicExprSafe(L->Ptr.get(), Param);
  }
  case VExpr::Old:
    return scalarDynamicExprSafe(static_cast<const VOldExpr *>(E)->Inner.get(),
                                 Param);
  case VExpr::Conditional: {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    if (C->Ty.Kind == VTypeKind::Ptr && referencesVar(C, Param))
      return false;
    return scalarDynamicExprSafe(C->Cond.get(), Param) &&
           scalarDynamicExprSafe(C->Then.get(), Param) &&
           scalarDynamicExprSafe(C->Else.get(), Param);
  }
  case VExpr::Forall:
  case VExpr::Exists: {
    const auto *Q = static_cast<const VQuantifiedExpr *>(E);
    return scalarDynamicExprSafe(Q->Lo.get(), Param) &&
           scalarDynamicExprSafe(Q->Hi.get(), Param) &&
           scalarDynamicExprSafe(Q->Body.get(), Param);
  }
  case VExpr::HeapStore: {
    const auto *H = static_cast<const VHeapStoreExpr *>(E);
    if (referencesVar(H->Ptr.get(), Param) &&
        !isDirectPointerParam(H->Ptr.get(), Param))
      return false;
    return !(H->Val->Ty.Kind == VTypeKind::Ptr &&
             referencesVar(H->Val.get(), Param)) &&
           scalarDynamicExprSafe(H->Ptr.get(), Param) &&
           scalarDynamicExprSafe(H->Val.get(), Param);
  }
  case VExpr::FieldAccess: {
    const auto *F = static_cast<const VFieldAccessExpr *>(E);
    return !referencesVar(F->Base.get(), Param) &&
           scalarDynamicExprSafe(F->Base.get(), Param);
  }
  case VExpr::SpecCall:
    return false;
  case VExpr::OverflowCheck: {
    const auto *O = static_cast<const VOverflowCheckExpr *>(E);
    return scalarDynamicExprSafe(O->Lhs.get(), Param) &&
           scalarDynamicExprSafe(O->Rhs.get(), Param);
  }
  }
  return false;
}

static bool scalarDynamicStmtSafe(const VStmt &S, const std::string &Param) {
  switch (S.K) {
  case VStmt::Assign: {
    const auto &A = static_cast<const VAssignStmt &>(S);
    return A.Target != Param &&
           !(A.Value->Ty.Kind == VTypeKind::Ptr &&
             referencesVar(A.Value.get(), Param)) &&
           scalarDynamicExprSafe(A.Value.get(), Param);
  }
  case VStmt::Store: {
    const auto &St = static_cast<const VStoreStmt &>(S);
    return (!referencesVar(St.Ptr.get(), Param) ||
            isDirectPointerParam(St.Ptr.get(), Param)) &&
           !(St.Value->Ty.Kind == VTypeKind::Ptr &&
             referencesVar(St.Value.get(), Param)) &&
           scalarDynamicExprSafe(St.Ptr.get(), Param) &&
           scalarDynamicExprSafe(St.Value.get(), Param);
  }
  case VStmt::Allocate: {
    const auto &A = static_cast<const VAllocateStmt &>(S);
    return A.Target != Param &&
           scalarDynamicExprSafe(A.Initializer.get(), Param);
  }
  case VStmt::Free:
    return !referencesVar(static_cast<const VFreeStmt &>(S).Ptr.get(), Param);
  case VStmt::If: {
    const auto &I = static_cast<const VIfStmt &>(S);
    if (!scalarDynamicExprSafe(I.Cond.get(), Param))
      return false;
    for (const auto &Nested : I.Then)
      if (!scalarDynamicStmtSafe(*Nested, Param))
        return false;
    for (const auto &Nested : I.Else)
      if (!scalarDynamicStmtSafe(*Nested, Param))
        return false;
    return true;
  }
  case VStmt::While: {
    const auto &W = static_cast<const VWhileStmt &>(S);
    if (!scalarDynamicExprSafe(W.Cond.get(), Param))
      return false;
    for (const auto &E : W.Invariants)
      if (!scalarDynamicExprSafe(E.get(), Param))
        return false;
    for (const auto &E : W.Decreases)
      if (!scalarDynamicExprSafe(E.get(), Param))
        return false;
    for (const auto &Nested : W.Body)
      if (!scalarDynamicStmtSafe(*Nested, Param))
        return false;
    return true;
  }
  case VStmt::Call:
    return false;
  case VStmt::Assert:
    return scalarDynamicExprSafe(static_cast<const VAssertStmt &>(S).Cond.get(),
                                 Param);
  case VStmt::Assume:
    return scalarDynamicExprSafe(static_cast<const VAssumeStmt &>(S).Cond.get(),
                                 Param);
  case VStmt::Return: {
    const auto &R = static_cast<const VReturnStmt &>(S);
    return !(R.Value && R.Value->Ty.Kind == VTypeKind::Ptr &&
             referencesVar(R.Value.get(), Param)) &&
           scalarDynamicExprSafe(R.Value.get(), Param);
  }
  case VStmt::Seq:
    for (const auto &Nested : static_cast<const VSeqStmt &>(S).Stmts)
      if (!scalarDynamicStmtSafe(*Nested, Param))
        return false;
    return true;
  case VStmt::GhostBlock:
    return false;
  case VStmt::ContractAssert:
    return scalarDynamicExprSafe(
        static_cast<const VContractAssertStmt &>(S).Cond.get(), Param);
  case VStmt::Havoc:
    return static_cast<const VHavocStmt &>(S).Target != Param;
  case VStmt::RevealWithFuel:
  case VStmt::HideSpec:
  case VStmt::RevealSpec:
    return true;
  }
  return false;
}

static bool scalarDynamicCalleeSafe(const VFunction &Fn,
                                    const std::string &Param) {
  for (unsigned I = 0;
       I < Fn.ExplicitPreconditionCount && I < Fn.Preconditions.size(); ++I)
    if (!scalarDynamicExprSafe(Fn.Preconditions[I].get(), Param))
      return false;
  for (const auto &E : Fn.Postconditions)
    if (!scalarDynamicExprSafe(E.get(), Param))
      return false;
  for (const auto &E : Fn.Modifies)
    if (!scalarDynamicExprSafe(E.get(), Param))
      return false;
  for (const auto &E : Fn.Recommends)
    if (!scalarDynamicExprSafe(E.get(), Param))
      return false;
  for (const auto &E : Fn.Decreases)
    if (!scalarDynamicExprSafe(E.get(), Param))
      return false;
  for (const auto &S : Fn.Body)
    if (!scalarDynamicStmtSafe(*S, Param))
      return false;
  return true;
}

static std::unique_ptr<VExpr> samePointerRegion(const VExpr *L, const VExpr *R,
                                                SourceLocation Loc) {
  auto LProvenance = pointerProvenance(L);
  auto RProvenance = pointerProvenance(R);
  if (LProvenance && RProvenance)
    return makeEq(std::move(LProvenance), std::move(RProvenance), Loc);
  if (LProvenance || RProvenance)
    return makeBoolLiteral(false, Loc);

  const VExpr *LBase = pointerBase(L);
  const VExpr *RBase = pointerBase(R);
  if (!LBase || !RBase || LBase->Ty.Kind != VTypeKind::Ptr ||
      RBase->Ty.Kind != VTypeKind::Ptr)
    return makeBoolLiteral(false, Loc);
  return makeEq(cloneVExpr(LBase), cloneVExpr(RBase), Loc);
}

static bool isRegionFootprint(const VExpr *E) {
  if (!E || E->K != VExpr::Load)
    return true;
  const VExpr *Ptr = static_cast<const VLoadExpr *>(E)->Ptr.get();
  while (Ptr && Ptr->K == VExpr::Cast)
    Ptr = static_cast<const VCastExpr *>(Ptr)->Inner.get();
  return !Ptr || Ptr->K == VExpr::Var;
}

static std::unique_ptr<VExpr> footprintContains(const VExpr *OuterPtr,
                                                bool OuterIsRegion,
                                                const VExpr *InnerPtr,
                                                bool InnerIsRegion,
                                                SourceLocation Loc) {
  if (OuterIsRegion)
    return samePointerRegion(OuterPtr, InnerPtr, Loc);
  if (InnerIsRegion)
    return makeBoolLiteral(false, Loc);
  return makeEq(cloneVExpr(OuterPtr), cloneVExpr(InnerPtr), Loc);
}

static std::unique_ptr<VExpr> nonNullSafety(const VExpr *Ptr,
                                            SourceLocation Loc) {
  const VExpr *Base = pointerBase(Ptr);
  if (!Base)
    return makeBoolLiteral(false, Loc);
  const VExpr *CheckedPointer = hasPointerProvenance(Ptr) ? Ptr : Base;
  auto NonNull = std::make_unique<VBinOpExpr>(
      VBinOp::Ne, cloneVExpr(CheckedPointer),
      std::make_unique<VLiteralExpr>(0, VType::makePtr(), Loc),
      VType::makeBool(), Loc);
  auto Valid = std::make_unique<VUnaryOpExpr>(
      VUnaryOp::ValidPtr, cloneVExpr(CheckedPointer), VType::makeBool(), Loc);
  return makeAnd(std::move(NonNull), std::move(Valid), Loc);
}

static std::unique_ptr<VExpr> initializedSafety(const VExpr *Ptr,
                                                SourceLocation Loc) {
  const VExpr *Base = pointerBase(Ptr);
  if (!Base)
    return makeBoolLiteral(false, Loc);
  const VExpr *CheckedPointer = hasPointerProvenance(Ptr) ? Ptr : Base;
  return std::make_unique<VUnaryOpExpr>(VUnaryOp::InitializedPtr,
                                        cloneVExpr(CheckedPointer),
                                        VType::makeBool(), Loc);
}

static std::unique_ptr<VExpr> safetyForExpr(const VExpr *E,
                                            const FunctionMap *FnMap) {
  if (!E)
    return makeBoolLiteral(false, SourceLocation());
  switch (E->K) {
  case VExpr::Literal:
  case VExpr::Var:
  case VExpr::Result:
    return makeBoolLiteral(true, E->Loc);
  case VExpr::BinOp: {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    auto Left = safetyForExpr(B->Lhs.get(), FnMap);
    auto Right = safetyForExpr(B->Rhs.get(), FnMap);
    if (B->Op == VBinOp::And)
      return combineSafety(
          std::move(Left),
          makeImplies(cloneVExpr(B->Lhs.get()), std::move(Right), B->Loc),
          B->Loc);
    if (B->Op == VBinOp::Or)
      return combineSafety(
          std::move(Left),
          makeImplies(makeNot(cloneVExpr(B->Lhs.get()), B->Loc),
                      std::move(Right), B->Loc),
          B->Loc);
    auto Safe = combineSafety(std::move(Left), std::move(Right), B->Loc);
    if (B->Op == VBinOp::Shl || B->Op == VBinOp::Shr)
      return combineSafety(std::move(Safe), shiftSafety(B), B->Loc);
    if (B->Op == VBinOp::Add || B->Op == VBinOp::Sub || B->Op == VBinOp::Mul)
      return combineSafety(std::move(Safe), signedArithmeticSafety(B), B->Loc);
    if (B->Op == VBinOp::Div || B->Op == VBinOp::Rem) {
      if (B->Lhs->Ty.IntMode != VIntMode::Machine)
        return Safe;
      auto NonZero = std::make_unique<VBinOpExpr>(
          VBinOp::Ne, cloneVExpr(B->Rhs.get()),
          std::make_unique<VLiteralExpr>(0, B->Rhs->Ty, B->Loc),
          VType::makeBool(), B->Loc);
      Safe = combineSafety(std::move(Safe), std::move(NonZero), B->Loc);
      if (isSignedMachineInteger(B->Lhs->Ty) && B->Lhs->Ty.BitWidth != 0) {
        auto IsMin = std::make_unique<VBinOpExpr>(
            VBinOp::Eq, cloneVExpr(B->Lhs.get()),
            std::make_unique<VLiteralExpr>(
                signedLimit(B->Lhs->Ty.BitWidth, true), B->Lhs->Ty, B->Loc),
            VType::makeBool(), B->Loc);
        auto IsMinusOne = std::make_unique<VBinOpExpr>(
            VBinOp::Eq, cloneVExpr(B->Rhs.get()),
            std::make_unique<VLiteralExpr>(-1, B->Rhs->Ty, B->Loc),
            VType::makeBool(), B->Loc);
        Safe = combineSafety(
            std::move(Safe),
            makeNot(makeAnd(std::move(IsMin), std::move(IsMinusOne), B->Loc),
                    B->Loc),
            B->Loc);
      }
    }
    return Safe;
  }
  case VExpr::UnaryOp: {
    const auto *U = static_cast<const VUnaryOpExpr *>(E);
    auto Safe = safetyForExpr(U->Operand.get(), FnMap);
    if (U->Op != VUnaryOp::Neg || !isSignedMachineInteger(U->Operand->Ty) ||
        U->Operand->Ty.BitWidth == 0)
      return Safe;
    auto NotMin = std::make_unique<VBinOpExpr>(
        VBinOp::Ne, cloneVExpr(U->Operand.get()),
        std::make_unique<VLiteralExpr>(
            signedLimit(U->Operand->Ty.BitWidth, true), U->Operand->Ty, U->Loc),
        VType::makeBool(), U->Loc);
    return combineSafety(std::move(Safe), std::move(NotMin), U->Loc);
  }
  case VExpr::Cast:
    return safetyForExpr(static_cast<const VCastExpr *>(E)->Inner.get(), FnMap);
  case VExpr::Load: {
    const auto *L = static_cast<const VLoadExpr *>(E);
    auto Safe = combineSafety(safetyForExpr(L->Ptr.get(), FnMap),
                              nonNullSafety(L->Ptr.get(), L->Loc), L->Loc);
    return combineSafety(std::move(Safe),
                         initializedSafety(L->Ptr.get(), L->Loc), L->Loc);
  }
  case VExpr::Old:
    return safetyForExpr(static_cast<const VOldExpr *>(E)->Inner.get(), FnMap);
  case VExpr::Conditional: {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    auto Safe = safetyForExpr(C->Cond.get(), FnMap);
    Safe =
        combineSafety(std::move(Safe),
                      makeImplies(cloneVExpr(C->Cond.get()),
                                  safetyForExpr(C->Then.get(), FnMap), C->Loc),
                      C->Loc);
    return combineSafety(std::move(Safe),
                         makeImplies(makeNot(cloneVExpr(C->Cond.get()), C->Loc),
                                     safetyForExpr(C->Else.get(), FnMap),
                                     C->Loc),
                         C->Loc);
  }
  case VExpr::OverflowCheck: {
    const auto *O = static_cast<const VOverflowCheckExpr *>(E);
    auto Safe = safetyForExpr(O->Lhs.get(), FnMap);
    if (O->Rhs)
      Safe = combineSafety(std::move(Safe), safetyForExpr(O->Rhs.get(), FnMap),
                           O->Loc);
    return Safe;
  }
  case VExpr::Forall:
  case VExpr::Exists: {
    const auto *Q = static_cast<const VQuantifiedExpr *>(E);
    auto Safe = combineSafety(safetyForExpr(Q->Lo.get(), FnMap),
                              safetyForExpr(Q->Hi.get(), FnMap), Q->Loc);
    auto BodySafe = safetyForExpr(Q->Body.get(), FnMap);
    auto Quantified = std::make_unique<VForallExpr>(
        Q->Binder, cloneVExpr(Q->Lo.get()), cloneVExpr(Q->Hi.get()),
        std::move(BodySafe), Q->Loc, Q->BinderType);
    return combineSafety(std::move(Safe), std::move(Quantified), Q->Loc);
  }
  case VExpr::HeapStore: {
    const auto *H = static_cast<const VHeapStoreExpr *>(E);
    auto Safe = combineSafety(safetyForExpr(H->Ptr.get(), FnMap),
                              safetyForExpr(H->Val.get(), FnMap), H->Loc);
    return combineSafety(std::move(Safe), nonNullSafety(H->Ptr.get(), H->Loc),
                         H->Loc);
  }
  case VExpr::FieldAccess:
    return safetyForExpr(static_cast<const VFieldAccessExpr *>(E)->Base.get(),
                         FnMap);
  case VExpr::SpecCall: {
    const auto *C = static_cast<const VSpecCallExpr *>(E);
    auto Safe = makeBoolLiteral(true, C->Loc);
    for (const auto &Arg : C->Args)
      Safe = combineSafety(std::move(Safe), safetyForExpr(Arg.get(), FnMap),
                           C->Loc);
    if (FnMap) {
      auto It = FnMap->find(C->CalleeIdentity);
      if (It != FnMap->end() && It->second->RequiresCallDefinedness) {
        if (It->second->NeedsDecreasesCheck)
          return combineSafety(std::move(Safe), makeBoolLiteral(false, C->Loc),
                               C->Loc);
        auto Expanded = SpecInliner(*FnMap, {}).inlineExpr(cloneVExpr(C));
        if (!Expanded || Expanded->K == VExpr::SpecCall)
          return combineSafety(std::move(Safe), makeBoolLiteral(false, C->Loc),
                               C->Loc);
        Safe = combineSafety(std::move(Safe),
                             safetyForExpr(Expanded.get(), FnMap), C->Loc);
      }
    }
    return Safe;
  }
  }
  return makeBoolLiteral(false, E->Loc);
}

static std::unique_ptr<VExpr>
machineMathBridgeForExpr(const VExpr *E, const FunctionMap *FnMap,
                         bool BridgeMachineValue = false) {
  if (!E)
    return makeBoolLiteral(true, SourceLocation());

  switch (E->K) {
  case VExpr::Literal:
  case VExpr::Var:
  case VExpr::Result:
    return makeBoolLiteral(true, E->Loc);
  case VExpr::BinOp: {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    bool BridgeLeft = BridgeMachineValue;
    bool BridgeRight = BridgeMachineValue;
    if (isIntegerType(B->Lhs->Ty) && isIntegerType(B->Rhs->Ty)) {
      if (B->Lhs->Ty.IntMode == VIntMode::Math &&
          B->Rhs->Ty.IntMode == VIntMode::Machine)
        BridgeRight = true;
      if (B->Rhs->Ty.IntMode == VIntMode::Math &&
          B->Lhs->Ty.IntMode == VIntMode::Machine)
        BridgeLeft = true;
    }
    auto Left = machineMathBridgeForExpr(B->Lhs.get(), FnMap, BridgeLeft);
    auto Right = machineMathBridgeForExpr(B->Rhs.get(), FnMap, BridgeRight);
    if (B->Op == VBinOp::And)
      return combineSafety(
          std::move(Left),
          makeImplies(cloneVExpr(B->Lhs.get()), std::move(Right), B->Loc),
          B->Loc);
    if (B->Op == VBinOp::Or)
      return combineSafety(
          std::move(Left),
          makeImplies(makeNot(cloneVExpr(B->Lhs.get()), B->Loc),
                      std::move(Right), B->Loc),
          B->Loc);

    auto Bridge = combineSafety(std::move(Left), std::move(Right), B->Loc);
    const bool LinearOperation =
        B->Op == VBinOp::Add || B->Op == VBinOp::Sub || B->Op == VBinOp::Div ||
        B->Op == VBinOp::Rem ||
        (B->Op == VBinOp::Mul &&
         (B->Lhs->K == VExpr::Literal || B->Rhs->K == VExpr::Literal));
    if (!BridgeMachineValue || !isSignedMachineInteger(B->Ty) ||
        !LinearOperation)
      return Bridge;

    VType MathTy = B->Ty;
    MathTy.IntMode = VIntMode::Math;
    auto MathValue = std::make_unique<VBinOpExpr>(
        B->Op, mathCast(B->Lhs.get()), mathCast(B->Rhs.get()), MathTy, B->Loc);
    auto Equality = makeEq(mathCast(B), std::move(MathValue), B->Loc);
    auto GuardedEquality =
        makeImplies(safetyForExpr(B, FnMap), std::move(Equality), B->Loc);
    return combineSafety(std::move(Bridge), std::move(GuardedEquality), B->Loc);
  }
  case VExpr::UnaryOp: {
    const auto *U = static_cast<const VUnaryOpExpr *>(E);
    auto Bridge =
        machineMathBridgeForExpr(U->Operand.get(), FnMap, BridgeMachineValue);
    if (!BridgeMachineValue || U->Op != VUnaryOp::Neg ||
        !isSignedMachineInteger(U->Ty))
      return Bridge;

    VType MathTy = U->Ty;
    MathTy.IntMode = VIntMode::Math;
    auto MathValue = std::make_unique<VUnaryOpExpr>(
        VUnaryOp::Neg, mathCast(U->Operand.get()), MathTy, U->Loc);
    auto Equality = makeEq(mathCast(U), std::move(MathValue), U->Loc);
    auto GuardedEquality =
        makeImplies(safetyForExpr(U, FnMap), std::move(Equality), U->Loc);
    return combineSafety(std::move(Bridge), std::move(GuardedEquality), U->Loc);
  }
  case VExpr::Cast: {
    const auto *C = static_cast<const VCastExpr *>(E);
    bool BridgeInner = BridgeMachineValue;
    if (isIntegerType(C->Ty) && C->Ty.IntMode == VIntMode::Math &&
        isIntegerType(C->Inner->Ty) &&
        C->Inner->Ty.IntMode == VIntMode::Machine)
      BridgeInner = true;
    return machineMathBridgeForExpr(C->Inner.get(), FnMap, BridgeInner);
  }
  case VExpr::Load:
    return machineMathBridgeForExpr(
        static_cast<const VLoadExpr *>(E)->Ptr.get(), FnMap, false);
  case VExpr::Old:
    return machineMathBridgeForExpr(
        static_cast<const VOldExpr *>(E)->Inner.get(), FnMap,
        BridgeMachineValue);
  case VExpr::Conditional: {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    auto Bridge = machineMathBridgeForExpr(C->Cond.get(), FnMap, false);
    Bridge =
        combineSafety(std::move(Bridge),
                      makeImplies(cloneVExpr(C->Cond.get()),
                                  machineMathBridgeForExpr(C->Then.get(), FnMap,
                                                           BridgeMachineValue),
                                  C->Loc),
                      C->Loc);
    Bridge =
        combineSafety(std::move(Bridge),
                      makeImplies(makeNot(cloneVExpr(C->Cond.get()), C->Loc),
                                  machineMathBridgeForExpr(C->Else.get(), FnMap,
                                                           BridgeMachineValue),
                                  C->Loc),
                      C->Loc);
    return Bridge;
  }
  case VExpr::OverflowCheck: {
    const auto *O = static_cast<const VOverflowCheckExpr *>(E);
    auto Bridge =
        machineMathBridgeForExpr(O->Lhs.get(), FnMap, BridgeMachineValue);
    if (O->Rhs)
      Bridge = combineSafety(
          std::move(Bridge),
          machineMathBridgeForExpr(O->Rhs.get(), FnMap, BridgeMachineValue),
          O->Loc);
    return Bridge;
  }
  case VExpr::Forall:
  case VExpr::Exists: {
    const auto *Q = static_cast<const VQuantifiedExpr *>(E);
    auto Bridge = combineSafety(
        machineMathBridgeForExpr(Q->Lo.get(), FnMap, false),
        machineMathBridgeForExpr(Q->Hi.get(), FnMap, false), Q->Loc);
    auto BodyBridge = machineMathBridgeForExpr(Q->Body.get(), FnMap, false);
    auto Quantified = std::make_unique<VForallExpr>(
        Q->Binder, cloneVExpr(Q->Lo.get()), cloneVExpr(Q->Hi.get()),
        std::move(BodyBridge), Q->Loc, Q->BinderType);
    return combineSafety(std::move(Bridge), std::move(Quantified), Q->Loc);
  }
  case VExpr::HeapStore: {
    const auto *H = static_cast<const VHeapStoreExpr *>(E);
    return combineSafety(
        machineMathBridgeForExpr(H->Ptr.get(), FnMap, false),
        machineMathBridgeForExpr(H->Val.get(), FnMap, BridgeMachineValue),
        H->Loc);
  }
  case VExpr::FieldAccess:
    return machineMathBridgeForExpr(
        static_cast<const VFieldAccessExpr *>(E)->Base.get(), FnMap,
        BridgeMachineValue);
  case VExpr::SpecCall: {
    const auto *C = static_cast<const VSpecCallExpr *>(E);
    auto Bridge = makeBoolLiteral(true, C->Loc);
    const VFunction *Callee = nullptr;
    if (FnMap) {
      auto It = FnMap->find(C->CalleeIdentity);
      if (It != FnMap->end())
        Callee = It->second;
    }
    for (size_t I = 0; I < C->Args.size(); ++I) {
      bool BridgeArg = false;
      if (Callee && I < Callee->Params.size()) {
        const VType &FormalTy = Callee->Params[I].second;
        BridgeArg = isIntegerType(FormalTy) &&
                    FormalTy.IntMode == VIntMode::Math &&
                    isIntegerType(C->Args[I]->Ty) &&
                    C->Args[I]->Ty.IntMode == VIntMode::Machine;
      }
      Bridge = combineSafety(
          std::move(Bridge),
          machineMathBridgeForExpr(C->Args[I].get(), FnMap, BridgeArg), C->Loc);
    }
    if (!Callee)
      return Bridge;

    if (!Callee->RequiresCallDefinedness || Callee->NeedsDecreasesCheck)
      return Bridge;
    auto Expanded = SpecInliner(*FnMap, {}).inlineExpr(cloneVExpr(C));
    if (!Expanded || Expanded->K == VExpr::SpecCall)
      return Bridge;
    return combineSafety(
        std::move(Bridge),
        machineMathBridgeForExpr(Expanded.get(), FnMap, BridgeMachineValue),
        C->Loc);
  }
  }
  return makeBoolLiteral(true, E->Loc);
}

static void collectDottedVars(const VExpr *E, std::set<std::string> &Out) {
  if (!E)
    return;
  switch (E->K) {
  case VExpr::Literal:
  case VExpr::Result:
    return;
  case VExpr::Var: {
    const auto &N = static_cast<const VVarExpr *>(E)->Name;
    if (N.find('.') != std::string::npos)
      Out.insert(N);
    return;
  }
  case VExpr::BinOp: {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    collectDottedVars(B->Lhs.get(), Out);
    collectDottedVars(B->Rhs.get(), Out);
    return;
  }
  case VExpr::UnaryOp:
    collectDottedVars(static_cast<const VUnaryOpExpr *>(E)->Operand.get(), Out);
    return;
  case VExpr::Cast:
    collectDottedVars(static_cast<const VCastExpr *>(E)->Inner.get(), Out);
    return;
  case VExpr::Load:
    collectDottedVars(static_cast<const VLoadExpr *>(E)->Ptr.get(), Out);
    return;
  case VExpr::Old:
    collectDottedVars(static_cast<const VOldExpr *>(E)->Inner.get(), Out);
    return;
  case VExpr::Conditional: {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    collectDottedVars(C->Cond.get(), Out);
    collectDottedVars(C->Then.get(), Out);
    collectDottedVars(C->Else.get(), Out);
    return;
  }
  case VExpr::OverflowCheck: {
    const auto *O = static_cast<const VOverflowCheckExpr *>(E);
    collectDottedVars(O->Lhs.get(), Out);
    collectDottedVars(O->Rhs.get(), Out);
    return;
  }
  case VExpr::FieldAccess: {
    const auto *F = static_cast<const VFieldAccessExpr *>(E);
    if (F->Base->K == VExpr::Var) {
      const auto &Base = static_cast<const VVarExpr *>(F->Base.get())->Name;
      Out.insert(Base + "." + F->Field);
    } else if (F->Base->K == VExpr::Result) {
      Out.insert("result." + F->Field);
    }
    collectDottedVars(F->Base.get(), Out);
    return;
  }
  case VExpr::SpecCall: {
    const auto *C = static_cast<const VSpecCallExpr *>(E);
    for (const auto &Arg : C->Args)
      collectDottedVars(Arg.get(), Out);
    return;
  }
  case VExpr::Forall:
  case VExpr::Exists: {
    const auto *Q = static_cast<const VQuantifiedExpr *>(E);
    collectDottedVars(Q->Lo.get(), Out);
    collectDottedVars(Q->Hi.get(), Out);
    collectDottedVars(Q->Body.get(), Out);
    return;
  }
  case VExpr::HeapStore: {
    const auto *H = static_cast<const VHeapStoreExpr *>(E);
    collectDottedVars(H->Ptr.get(), Out);
    collectDottedVars(H->Val.get(), Out);
    return;
  }
  }
}

static std::unique_ptr<VExpr> substParams(
    const VExpr *E, const std::map<std::string, std::unique_ptr<VExpr>> &Map,
    const CloneCtx &Ctx, const std::string &EntryHeap,
    const std::string &HeapOverride = "", std::set<std::string> BoundVars = {},
    const std::map<std::string, std::unique_ptr<VExpr>> *OldMap = nullptr) {
  if (!E)
    return nullptr;
  switch (E->K) {
  case VExpr::Literal:
    return cloneVExpr(E);
  case VExpr::Var: {
    const auto *V = static_cast<const VVarExpr *>(E);
    if (!BoundVars.count(V->Name))
      if (auto It = Map.find(V->Name); It != Map.end())
        return cloneVExpr(It->second.get());
    return cloneExpr(E, Ctx);
  }
  case VExpr::BinOp: {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    return std::make_unique<VBinOpExpr>(
        B->Op,
        substParams(B->Lhs.get(), Map, Ctx, EntryHeap, HeapOverride, BoundVars,
                    OldMap),
        substParams(B->Rhs.get(), Map, Ctx, EntryHeap, HeapOverride, BoundVars,
                    OldMap),
        B->Ty, B->Loc);
  }
  case VExpr::UnaryOp: {
    const auto *U = static_cast<const VUnaryOpExpr *>(E);
    return std::make_unique<VUnaryOpExpr>(
        U->Op,
        substParams(U->Operand.get(), Map, Ctx, EntryHeap, HeapOverride,
                    BoundVars, OldMap),
        U->Ty, U->Loc,
        stateHeapName(Ctx, VAllocationHeapName, U->AllocationHeapVar),
        stateHeapName(Ctx, VLivenessHeapName, U->LivenessHeapVar),
        stateHeapName(Ctx, VInitializationHeapName, U->InitializationHeapVar));
  }
  case VExpr::Cast: {
    const auto *C = static_cast<const VCastExpr *>(E);
    return std::make_unique<VCastExpr>(substParams(C->Inner.get(), Map, Ctx,
                                                   EntryHeap, HeapOverride,
                                                   BoundVars, OldMap),
                                       C->FromTy, C->Ty, C->Loc);
  }
  case VExpr::Load: {
    const auto *L = static_cast<const VLoadExpr *>(E);
    std::string Heap =
        HeapOverride.empty() ? Ctx.Renames.at(VHeapName) : HeapOverride;
    return std::make_unique<VLoadExpr>(substParams(L->Ptr.get(), Map, Ctx,
                                                   EntryHeap, HeapOverride,
                                                   BoundVars, OldMap),
                                       L->Ty, L->Loc, std::move(Heap));
  }
  case VExpr::Result: {
    if (auto It = Map.find("result"); It != Map.end())
      return cloneVExpr(It->second.get());
    return cloneExpr(E, Ctx);
  }
  case VExpr::Old: {
    const auto *O = static_cast<const VOldExpr *>(E);
    const auto &EntryMap = OldMap ? *OldMap : Map;
    return substParams(O->Inner.get(), EntryMap, Ctx, EntryHeap, EntryHeap,
                       std::move(BoundVars), OldMap);
  }
  case VExpr::Conditional: {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    return std::make_unique<VConditionalExpr>(
        substParams(C->Cond.get(), Map, Ctx, EntryHeap, HeapOverride, BoundVars,
                    OldMap),
        substParams(C->Then.get(), Map, Ctx, EntryHeap, HeapOverride, BoundVars,
                    OldMap),
        substParams(C->Else.get(), Map, Ctx, EntryHeap, HeapOverride, BoundVars,
                    OldMap),
        C->Ty, C->Loc);
  }
  case VExpr::FieldAccess: {
    const auto *F = static_cast<const VFieldAccessExpr *>(E);
    return std::make_unique<VFieldAccessExpr>(
        substParams(F->Base.get(), Map, Ctx, EntryHeap, HeapOverride, BoundVars,
                    OldMap),
        F->Field, F->Ty, F->Loc);
  }
  case VExpr::SpecCall: {
    const auto *C = static_cast<const VSpecCallExpr *>(E);
    std::vector<std::unique_ptr<VExpr>> Args;
    for (const auto &Arg : C->Args)
      Args.push_back(substParams(Arg.get(), Map, Ctx, EntryHeap, HeapOverride,
                                 BoundVars, OldMap));
    return std::make_unique<VSpecCallExpr>(C->Callee, C->CalleeIdentity,
                                           std::move(Args), C->Ty, C->Loc);
  }
  case VExpr::OverflowCheck: {
    const auto *O = static_cast<const VOverflowCheckExpr *>(E);
    return std::make_unique<VOverflowCheckExpr>(
        O->Op,
        substParams(O->Lhs.get(), Map, Ctx, EntryHeap, HeapOverride, BoundVars,
                    OldMap),
        O->Rhs ? substParams(O->Rhs.get(), Map, Ctx, EntryHeap, HeapOverride,
                             BoundVars, OldMap)
               : nullptr,
        O->Loc);
  }
  case VExpr::Forall:
  case VExpr::Exists: {
    const auto *Q = static_cast<const VQuantifiedExpr *>(E);
    std::set<std::string> BodyBound = BoundVars;
    BodyBound.insert(Q->Binder);
    auto Lo = substParams(Q->Lo.get(), Map, Ctx, EntryHeap, HeapOverride,
                          BoundVars, OldMap);
    auto Hi = substParams(Q->Hi.get(), Map, Ctx, EntryHeap, HeapOverride,
                          BoundVars, OldMap);
    auto Body = substParams(Q->Body.get(), Map, Ctx, EntryHeap, HeapOverride,
                            std::move(BodyBound), OldMap);
    if (E->K == VExpr::Forall)
      return std::make_unique<VForallExpr>(Q->Binder, std::move(Lo),
                                           std::move(Hi), std::move(Body),
                                           Q->Loc, Q->BinderType);
    return std::make_unique<VExistsExpr>(Q->Binder, std::move(Lo),
                                         std::move(Hi), std::move(Body), Q->Loc,
                                         Q->BinderType);
  }
  case VExpr::HeapStore: {
    const auto *H = static_cast<const VHeapStoreExpr *>(E);
    return std::make_unique<VHeapStoreExpr>(
        H->HeapBefore, H->HeapAfter,
        substParams(H->Ptr.get(), Map, Ctx, EntryHeap, HeapOverride, BoundVars,
                    OldMap),
        substParams(H->Val.get(), Map, Ctx, EntryHeap, HeapOverride, BoundVars,
                    OldMap),
        H->Loc);
  }
  }
  return nullptr;
}

class PassivizerImpl {
  struct ReturnCase {
    std::unique_ptr<VExpr> Guard;
    std::unique_ptr<VExpr> Value;
    SourceLocation Loc;
  };
  struct FieldReturnCase {
    std::unique_ptr<VExpr> Guard;
    std::map<std::string, std::unique_ptr<VExpr>> Values;
    SourceLocation Loc;
  };

  std::map<std::string, int> Versions;
  std::map<std::string, VType> Types;
  std::map<std::string, std::unique_ptr<VExpr>> OldState;
  std::vector<ReturnCase> ReturnCases;
  std::vector<FieldReturnCase> FieldReturnCases;
  std::vector<std::unique_ptr<VExpr>> ReturnGuards;
  std::vector<std::string> OwnedAllocationIdentities;
  std::string ResultVar = "__result";
  const VFunction &Fn;
  FunctionMap FnMap;

  std::string versionedName(const std::string &N) {
    int &V = Versions[N];
    return N + "_" + std::to_string(V);
  }

  std::string bump(const std::string &N) {
    return N + "_" + std::to_string(++Versions[N]);
  }

  static void emitPassive(PassiveProgram &P, PassiveStmt::Kind K,
                          std::unique_ptr<VExpr> Cond,
                          const VExpr *Guard = nullptr,
                          SourceLocation Loc = SourceLocation()) {
    auto PS = std::make_unique<PassiveStmt>();
    PS->K = K;
    if (Guard)
      Cond = makeImplies(cloneVExpr(Guard), std::move(Cond), Loc);
    PS->Cond = std::move(Cond);
    P.Stmts.push_back(std::move(PS));
  }

  static void appendProgram(PassiveProgram &P, PassiveProgram &Branch) {
    for (auto &S : Branch.Stmts)
      P.Stmts.push_back(std::move(S));
  }

  void finalizeReturns(PassiveProgram &P,
                       std::map<std::string, std::string> &Renames,
                       const VExpr *Active) {
    if (Fn.ReturnType.Kind == VTypeKind::Void && Active)
      ReturnGuards.push_back(cloneVExpr(Active));

    std::unique_ptr<VExpr> Coverage = makeBoolLiteral(false, SourceLocation());
    for (const auto &Guard : ReturnGuards)
      Coverage =
          makeOr(std::move(Coverage), cloneVExpr(Guard.get()), Guard->Loc);
    emitPassive(P, PassiveStmt::Assert, std::move(Coverage));

    if (Fn.ReturnType.Kind == VTypeKind::Void)
      return;

    if (!FieldReturnCases.empty()) {
      std::set<std::string> Fields;
      for (const auto &Case : FieldReturnCases)
        for (const auto &Value : Case.Values)
          Fields.insert(Value.first);
      for (const std::string &Field : Fields) {
        VType Ty = VType::makeInt32(Fn.IntMode);
        for (const auto &Case : FieldReturnCases)
          if (auto It = Case.Values.find(Field); It != Case.Values.end()) {
            Ty = It->second->Ty;
            break;
          }
        std::unique_ptr<VExpr> Result =
            std::make_unique<VLiteralExpr>(0, Ty, SourceLocation());
        for (auto It = FieldReturnCases.rbegin(); It != FieldReturnCases.rend();
             ++It) {
          auto Value = It->Values.find(Field);
          if (Value == It->Values.end())
            continue;
          Result = std::make_unique<VConditionalExpr>(
              cloneVExpr(It->Guard.get()), cloneVExpr(Value->second.get()),
              std::move(Result), Ty, It->Loc);
        }
        std::string ResultName = bump(Field);
        Renames[Field] = ResultName;
        Types[Field] = Ty;
        emitMathBridge(P, Result.get(), nullptr, SourceLocation(), true);
        emitPassive(
            P, PassiveStmt::Assume,
            makeEq(std::make_unique<VVarExpr>(ResultName, Ty, SourceLocation()),
                   std::move(Result), SourceLocation()));
      }
      return;
    }

    std::unique_ptr<VExpr> Result =
        std::make_unique<VLiteralExpr>(0, Fn.ReturnType, SourceLocation());
    for (auto It = ReturnCases.rbegin(); It != ReturnCases.rend(); ++It) {
      Result = std::make_unique<VConditionalExpr>(
          cloneVExpr(It->Guard.get()), cloneVExpr(It->Value.get()),
          std::move(Result), Fn.ReturnType, It->Loc);
    }
    std::string ResultName = bump(ResultVar);
    Renames["result"] = ResultName;
    emitMathBridge(P, Result.get(), nullptr, SourceLocation(), true);
    emitPassive(P, PassiveStmt::Assume,
                makeEq(std::make_unique<VVarExpr>(ResultName, Fn.ReturnType,
                                                  SourceLocation()),
                       std::move(Result), SourceLocation()));
    P.ResultVarName = ResultName;
  }

  void collectModified(const VStmt &S, std::set<std::string> &Out) const {
    switch (S.K) {
    case VStmt::Assign:
      Out.insert(static_cast<const VAssignStmt &>(S).Target);
      break;
    case VStmt::Store:
      Out.insert(VHeapName);
      break;
    case VStmt::Allocate: {
      const auto &A = static_cast<const VAllocateStmt &>(S);
      Out.insert(A.Target);
      Out.insert(A.ProvenanceTarget);
      Out.insert(VHeapName);
      Out.insert(VAllocationHeapName);
      Out.insert(VAllocationBaseHeapName);
      Out.insert(VLivenessHeapName);
      Out.insert(VAllocationUsedHeapName);
      Out.insert(VInitializationHeapName);
      Out.insert(VAllocationSizeHeapName);
      Out.insert(VAllocationAlignHeapName);
      break;
    }
    case VStmt::Free:
      Out.insert(VLivenessHeapName);
      break;
    case VStmt::If: {
      const auto &I = static_cast<const VIfStmt &>(S);
      for (const auto &Then : I.Then)
        collectModified(*Then, Out);
      for (const auto &Else : I.Else)
        collectModified(*Else, Out);
      break;
    }
    case VStmt::While: {
      const auto &W = static_cast<const VWhileStmt &>(S);
      for (const auto &Body : W.Body)
        collectModified(*Body, Out);
      break;
    }
    case VStmt::Call: {
      const auto &C = static_cast<const VCallStmt &>(S);
      auto Callee = FnMap.find(C.CalleeIdentity);
      if (!C.ResultTarget.empty()) {
        if (Callee != FnMap.end() &&
            Callee->second->ReturnType.Kind == VTypeKind::Struct) {
          for (const auto &Field : Callee->second->ReturnFields)
            Out.insert(C.ResultTarget + "." + Field.first);
        } else {
          Out.insert(C.ResultTarget);
        }
      }
      if (Callee != FnMap.end() && !Callee->second->Modifies.empty())
        Out.insert(VHeapName);
      break;
    }
    case VStmt::GhostBlock:
      for (const auto &Body : static_cast<const VGhostBlockStmt &>(S).Body)
        collectModified(*Body, Out);
      break;
    case VStmt::Seq:
      for (const auto &Body : static_cast<const VSeqStmt &>(S).Stmts)
        collectModified(*Body, Out);
      break;
    case VStmt::Assert:
    case VStmt::Assume:
    case VStmt::Return:
    case VStmt::RevealWithFuel:
    case VStmt::HideSpec:
    case VStmt::RevealSpec:
    case VStmt::ContractAssert:
      break;
    case VStmt::Havoc:
      Out.insert(static_cast<const VHavocStmt &>(S).Target);
      break;
    }
  }

  bool containsReturn(const VStmt &S) const {
    if (S.K == VStmt::Return)
      return true;
    if (S.K == VStmt::If) {
      const auto &I = static_cast<const VIfStmt &>(S);
      for (const auto &BranchStmt : I.Then)
        if (containsReturn(*BranchStmt))
          return true;
      for (const auto &BranchStmt : I.Else)
        if (containsReturn(*BranchStmt))
          return true;
    } else if (S.K == VStmt::While) {
      for (const auto &Body : static_cast<const VWhileStmt &>(S).Body)
        if (containsReturn(*Body))
          return true;
    } else if (S.K == VStmt::GhostBlock) {
      for (const auto &Body : static_cast<const VGhostBlockStmt &>(S).Body)
        if (containsReturn(*Body))
          return true;
    } else if (S.K == VStmt::Seq) {
      for (const auto &Body : static_cast<const VSeqStmt &>(S).Stmts)
        if (containsReturn(*Body))
          return true;
    }
    return false;
  }

  VType typeForName(const std::string &Name) const {
    if (auto It = Types.find(Name); It != Types.end())
      return It->second;
    return VType::makeInt32(Fn.IntMode);
  }

  void emitExprSafety(PassiveProgram &P, const VExpr *E, const VExpr *Guard,
                      SourceLocation Loc,
                      const std::map<std::string, std::string> &Renames,
                      bool BridgeMachineValue = false) {
    auto Safety = safetyForExpr(E, &FnMap);
    CloneCtx Ctx{Renames, OldState, false};
    emitPassive(P, PassiveStmt::Assert, cloneExpr(Safety.get(), Ctx), Guard,
                Loc);
    emitPassive(P, PassiveStmt::Assume,
                machineMathBridgeForExpr(E, &FnMap, BridgeMachineValue), Guard,
                Loc);
  }

  void emitMathBridge(PassiveProgram &P, const VExpr *E, const VExpr *Guard,
                      SourceLocation Loc, bool BridgeMachineValue = false) {
    emitPassive(P, PassiveStmt::Assume,
                machineMathBridgeForExpr(E, &FnMap, BridgeMachineValue), Guard,
                Loc);
  }

  void updateHeap(PassiveProgram &P,
                  std::map<std::string, std::string> &Renames,
                  const char *HeapName, std::unique_ptr<VExpr> Ptr,
                  std::unique_ptr<VExpr> Value, const VExpr *Guard,
                  SourceLocation Loc) {
    const std::string Before = Renames[HeapName];
    const std::string After = bump(HeapName);
    Renames[HeapName] = After;
    emitPassive(P, PassiveStmt::Assume,
                std::make_unique<VHeapStoreExpr>(Before, After, std::move(Ptr),
                                                 std::move(Value), Loc),
                Guard, Loc);
  }

  static std::unique_ptr<VExpr>
  addressOffset(const VExpr *Base, uint64_t Offset, SourceLocation Loc) {
    if (Offset == 0)
      return cloneVExpr(Base);
    return std::make_unique<VBinOpExpr>(
        VBinOp::Add, cloneVExpr(Base),
        std::make_unique<VLiteralExpr>(std::to_string(Offset), VType::makePtr(),
                                       Loc),
        VType::makePtr(), Loc);
  }

public:
  PassivizerImpl(const VFunction &Fn, FunctionMap FnMap)
      : Fn(Fn), FnMap(std::move(FnMap)) {}

  PassiveProgram run() {
    PassiveProgram P;
    CloneCtx Ctx{{}, OldState, false};

    const char *StateHeaps[] = {VHeapName,
                                VAllocationHeapName,
                                VAllocationBaseHeapName,
                                VLivenessHeapName,
                                VAllocationUsedHeapName,
                                VInitializationHeapName,
                                VAllocationSizeHeapName,
                                VAllocationAlignHeapName};
    for (const char *Heap : StateHeaps) {
      Versions[Heap] = 0;
      Types[Heap] = VType::makePtr();
    }
    Types["result"] = Fn.ReturnType;
    for (const auto &Param : Fn.Params)
      Types[Param.first] = Param.second;
    std::string Heap0 = versionedName(VHeapName);

    std::map<std::string, std::string> Renames;
    for (const char *Heap : StateHeaps) {
      std::string Heap0Name = versionedName(Heap);
      OldState[Heap] = std::make_unique<VVarExpr>(Heap0Name, VType::makePtr(),
                                                  SourceLocation());
      Renames[Heap] = Heap0Name;
    }

    for (const auto &Param : Fn.Params) {
      std::string V0 = versionedName(Param.first);
      OldState[Param.first] =
          std::make_unique<VVarExpr>(V0, Param.second, SourceLocation());
      Renames[Param.first] = V0;
    }

    std::set<std::string> FieldVars;
    for (const auto &Pre : Fn.Preconditions)
      collectDottedVars(Pre.get(), FieldVars);
    for (const auto &Post : Fn.Postconditions)
      collectDottedVars(Post.get(), FieldVars);
    for (const std::string &FV : FieldVars) {
      if (OldState.count(FV))
        continue;
      std::string V0 = versionedName(FV);
      OldState[FV] = std::make_unique<VVarExpr>(
          V0, VType::makeInt32(Fn.IntMode), SourceLocation());
      Renames[FV] = V0;
    }

    for (const auto &Pre : Fn.Preconditions) {
      CloneCtx PCtx{Renames, OldState, false};
      P.EntryAssumes.push_back(cloneExpr(Pre.get(), PCtx));
    }
    {
      auto Null =
          std::make_unique<VLiteralExpr>(0, VType::makePtr(), SourceLocation());
      auto NullOwner = std::make_unique<VLoadExpr>(
          cloneVExpr(Null.get()), VType::makePtr(), SourceLocation(),
          Renames[VAllocationHeapName]);
      P.EntryAssumes.push_back(makeEq(
          std::move(NullOwner), cloneVExpr(Null.get()), SourceLocation()));
      auto NullLive = std::make_unique<VLoadExpr>(
          std::move(Null), VType::makeBool(), SourceLocation(),
          Renames[VLivenessHeapName]);
      P.EntryAssumes.push_back(makeNot(std::move(NullLive), SourceLocation()));
    }

    std::unique_ptr<VExpr> Active = makeBoolLiteral(true, SourceLocation());
    for (const auto &S : Fn.Body)
      processStmt(*S, P, Renames, Active);
    finalizeReturns(P, Renames, Active.get());

    for (const auto &Post : Fn.Postconditions) {
      CloneCtx PCtx{Renames, OldState, false};
      auto BoundPost = cloneExpr(Post.get(), PCtx);
      emitMathBridge(P, BoundPost.get(), nullptr, BoundPost->Loc);
      auto Safety = safetyForExpr(BoundPost.get(), &FnMap);
      P.ExitAsserts.push_back(cloneExpr(Safety.get(), PCtx));
      P.ExitAsserts.push_back(std::move(BoundPost));
    }
    P.OldHeapName = Heap0;
    P.SpecFunctions = FnMap;
    P.SpecFuel = Fn.SpecFuel;
    P.HiddenSpecs = Fn.HiddenSpecs;
    P.RevealedSpecs = Fn.RevealedSpecs;
    P.CallerIntMode = Fn.IntMode;
    return P;
  }

  void emitCallStmt(const VCallStmt &C, PassiveProgram &P,
                    std::map<std::string, std::string> &Renames) {
    auto CalleeIt = FnMap.find(C.CalleeIdentity);
    if (CalleeIt == FnMap.end()) {
      emitPassive(P, PassiveStmt::Assert, makeBoolLiteral(false, C.Loc));
      return;
    }
    const VFunction *Callee = CalleeIt->second;
    if (Callee->IsSpec)
      return;
    if (Callee->UsesDynamicStorage) {
      emitPassive(P, PassiveStmt::Assert, makeBoolLiteral(false, C.Loc));
      return;
    }
    const std::string EntryHeap = Renames[VHeapName];
    CloneCtx Ctx{Renames, OldState, false};
    std::map<std::string, std::unique_ptr<VExpr>> ParamMap;
    for (unsigned I = 0; I < Callee->Params.size() && I < C.Args.size(); ++I)
      ParamMap[Callee->Params[I].first] = cloneExpr(C.Args[I].get(), Ctx);
    for (const auto &Param : Callee->Params)
      if (auto It = ParamMap.find(Param.first);
          It != ParamMap.end() && hasPointerProvenance(It->second.get()) &&
          (Callee->IsProof || Callee->IsExternalContract ||
           Callee->ReturnType.Kind == VTypeKind::Ptr ||
           !scalarDynamicCalleeSafe(*Callee, Param.first))) {
        emitPassive(P, PassiveStmt::Assert, makeBoolLiteral(false, C.Loc));
        return;
      }
    for (const auto &Arg : ParamMap)
      emitExprSafety(P, Arg.second.get(), nullptr, C.Loc, Renames, true);

    std::vector<std::unique_ptr<VExpr>> ActualModifies;
    for (const auto &M : Callee->Modifies)
      ActualModifies.push_back(
          substParams(M.get(), ParamMap, Ctx, EntryHeap, EntryHeap));
    std::vector<std::unique_ptr<VExpr>> CallerModifies;
    CloneCtx CallerEntryCtx{Renames, OldState, true};
    for (const auto &M : Fn.Modifies)
      CallerModifies.push_back(cloneExpr(M.get(), CallerEntryCtx));

    for (const auto &Pre : Callee->Preconditions) {
      auto BoundPre = substParams(Pre.get(), ParamMap, Ctx, EntryHeap);
      emitExprSafety(P, BoundPre.get(), nullptr, C.Loc, Renames);
      auto PS = std::make_unique<PassiveStmt>();
      PS->K = PassiveStmt::Assert;
      PS->Cond = std::move(BoundPre);
      P.Stmts.push_back(std::move(PS));
    }

    for (size_t I = 0; I < ActualModifies.size(); ++I) {
      const auto &M = ActualModifies[I];
      emitExprSafety(P, M.get(), nullptr, M->Loc, Renames);
      auto Allowed = makeBoolLiteral(false, C.Loc);
      const auto *ActualLoad = M && M->K == VExpr::Load
                                   ? static_cast<const VLoadExpr *>(M.get())
                                   : nullptr;
      if (ActualLoad) {
        const bool ActualIsRegion =
            I >= Callee->Modifies.size() ||
            isRegionFootprint(Callee->Modifies[I].get());
        if (hasPointerProvenance(ActualLoad->Ptr.get()))
          Allowed =
              makeOr(std::move(Allowed), makeBoolLiteral(true, C.Loc), C.Loc);
        for (size_t J = 0; J < CallerModifies.size(); ++J) {
          const auto &CallerM = CallerModifies[J];
          if (const auto *CallerLoad =
                  CallerM && CallerM->K == VExpr::Load
                      ? static_cast<const VLoadExpr *>(CallerM.get())
                      : nullptr)
            Allowed = makeOr(
                std::move(Allowed),
                footprintContains(CallerLoad->Ptr.get(),
                                  J >= Fn.Modifies.size() ||
                                      isRegionFootprint(Fn.Modifies[J].get()),
                                  ActualLoad->Ptr.get(), ActualIsRegion, C.Loc),
                C.Loc);
        }
      }
      emitPassive(P, PassiveStmt::Assert, std::move(Allowed), nullptr, C.Loc);
    }

    if (Callee->ReturnType.Kind != VTypeKind::Void) {
      const std::string ResultTarget =
          C.ResultTarget.empty() ? "__discarded_call_result" : C.ResultTarget;
      if (Callee->ReturnType.Kind == VTypeKind::Struct) {
        for (const auto &[Field, Ty] : Callee->ReturnFields) {
          const std::string TargetField = ResultTarget + "." + Field;
          std::string RetVer = bump(TargetField);
          if (!C.ResultTarget.empty())
            Renames[TargetField] = RetVer;
          Types[TargetField] = Ty;
          ParamMap["result." + Field] =
              std::make_unique<VVarExpr>(RetVer, Ty, C.Loc);
        }
      } else {
        std::string RetVer = bump(ResultTarget);
        if (!C.ResultTarget.empty())
          Renames[ResultTarget] = RetVer;
        Types[ResultTarget] = Callee->ReturnType;
        ParamMap["result"] =
            std::make_unique<VVarExpr>(RetVer, Callee->ReturnType, C.Loc);
      }
    }

    bool HasPointerParam = false;
    for (const auto &Param : Callee->Params)
      HasPointerParam |= Param.second.Kind == VTypeKind::Ptr;
    bool CanFrameExactly = !ActualModifies.empty();
    for (size_t I = 0; I < ActualModifies.size(); ++I)
      if (!ActualModifies[I] || ActualModifies[I]->K != VExpr::Load ||
          I >= Callee->Modifies.size() ||
          isRegionFootprint(Callee->Modifies[I].get()))
        CanFrameExactly = false;
    if ((!ActualModifies.empty() && !CanFrameExactly) ||
        (ActualModifies.empty() && HasPointerParam)) {
      Renames[VHeapName] = bump(VHeapName);
    } else if (CanFrameExactly) {
      std::string PreviousHeap = EntryHeap;
      for (const auto &M : ActualModifies) {
        const auto *L = static_cast<const VLoadExpr *>(M.get());
        std::string NextHeap = bump(VHeapName);
        auto Fresh =
            std::make_unique<VVarExpr>(bump("__call_heap_value"), L->Ty, C.Loc);
        emitPassive(P, PassiveStmt::Assume,
                    std::make_unique<VHeapStoreExpr>(PreviousHeap, NextHeap,
                                                     cloneVExpr(L->Ptr.get()),
                                                     std::move(Fresh), C.Loc));
        PreviousHeap = NextHeap;
      }
      Renames[VHeapName] = PreviousHeap;
    }

    std::map<std::string, std::unique_ptr<VExpr>> PostParamMap;
    for (const auto &[Name, Value] : ParamMap)
      PostParamMap[Name] = cloneVExpr(Value.get());
    std::set<std::string> ModifiedParams;
    for (const auto &S : Callee->Body)
      collectModified(*S, ModifiedParams);
    for (const auto &[Name, Ty] : Callee->Params)
      if (ModifiedParams.count(Name))
        PostParamMap[Name] =
            std::make_unique<VVarExpr>(bump("__call_final_param"), Ty, C.Loc);

    for (const auto &Post : Callee->Postconditions) {
      auto PS = std::make_unique<PassiveStmt>();
      PS->K = PassiveStmt::Assume;
      PS->Cond = substParams(Post.get(), PostParamMap, Ctx, EntryHeap, "", {},
                             &ParamMap);
      P.Stmts.push_back(std::move(PS));
    }
  }

  void processStmt(const VStmt &S, PassiveProgram &P,
                   std::map<std::string, std::string> &Renames,
                   std::unique_ptr<VExpr> &Active) {
    switch (S.K) {
    case VStmt::Assign: {
      const auto &A = static_cast<const VAssignStmt &>(S);
      CloneCtx Ctx{Renames, OldState, false};
      auto Val = cloneExpr(A.Value.get(), Ctx);
      emitExprSafety(P, Val.get(), Active.get(), A.Loc, Renames, true);
      Types[A.Target] = Val->Ty;
      std::string NewName = bump(A.Target);
      Renames[A.Target] = NewName;
      VType ValueTy = Val->Ty;
      emitPassive(P, PassiveStmt::Assume,
                  makeEq(std::make_unique<VVarExpr>(NewName, ValueTy, A.Loc),
                         std::move(Val), A.Loc),
                  Active.get(), A.Loc);
      break;
    }
    case VStmt::Store: {
      const auto &St = static_cast<const VStoreStmt &>(S);
      CloneCtx Ctx{Renames, OldState, false};
      auto Ptr = cloneExpr(St.Ptr.get(), Ctx);
      auto Val = cloneExpr(St.Value.get(), Ctx);
      emitExprSafety(P, Ptr.get(), Active.get(), St.Loc, Renames);
      emitExprSafety(P, Val.get(), Active.get(), St.Loc, Renames, true);
      auto StoreSafety = nonNullSafety(Ptr.get(), St.Loc);
      emitPassive(P, PassiveStmt::Assert, cloneExpr(StoreSafety.get(), Ctx),
                  Active.get(), St.Loc);
      auto Allowed = makeBoolLiteral(false, St.Loc);
      CloneCtx EntryCtx{Renames, OldState, true};
      for (const auto &M : Fn.Modifies)
        if (const auto *Load = M && M->K == VExpr::Load
                                   ? static_cast<const VLoadExpr *>(M.get())
                                   : nullptr) {
          auto DeclaredPtr = cloneExpr(Load->Ptr.get(), EntryCtx);
          Allowed = makeOr(std::move(Allowed),
                           footprintContains(DeclaredPtr.get(),
                                             isRegionFootprint(M.get()),
                                             Ptr.get(), false, St.Loc),
                           St.Loc);
        }
      if (auto Provenance = pointerProvenance(Ptr.get()))
        for (const std::string &Identity : OwnedAllocationIdentities)
          Allowed = makeOr(std::move(Allowed),
                           makeEq(cloneVExpr(Provenance.get()),
                                  std::make_unique<VVarExpr>(
                                      Identity, VType::makePtr(), St.Loc),
                                  St.Loc),
                           St.Loc);
      emitPassive(P, PassiveStmt::Assert, std::move(Allowed), Active.get(),
                  St.Loc);
      std::string OldHeap = Renames[VHeapName];
      std::string NewHeap = bump(VHeapName);
      Renames[VHeapName] = NewHeap;
      emitPassive(P, PassiveStmt::Assume,
                  std::make_unique<VHeapStoreExpr>(
                      OldHeap, NewHeap, std::move(Ptr), std::move(Val), St.Loc),
                  Active.get(), St.Loc);
      if (hasPointerProvenance(St.Ptr.get()))
        updateHeap(P, Renames, VInitializationHeapName,
                   cloneExpr(St.Ptr.get(), Ctx), makeBoolLiteral(true, St.Loc),
                   Active.get(), St.Loc);
      break;
    }
    case VStmt::Allocate: {
      const auto &A = static_cast<const VAllocateStmt &>(S);
      if (A.ProvenanceTarget.empty()) {
        emitPassive(P, PassiveStmt::Assert, makeBoolLiteral(false, A.Loc),
                    Active.get(), A.Loc);
        break;
      }
      CloneCtx Ctx{Renames, OldState, false};
      std::unique_ptr<VExpr> Initializer;
      if (A.Initializer) {
        Initializer = cloneExpr(A.Initializer.get(), Ctx);
        emitExprSafety(P, Initializer.get(), Active.get(), A.Loc, Renames,
                       true);
      }

      Types[A.Target] = VType::makePtr(A.SizeBytes);
      Types[A.ProvenanceTarget] = VType::makePtr();
      const std::string PointerName = bump(A.Target);
      const std::string ProvenanceName = bump(A.ProvenanceTarget);
      Renames[A.Target] = PointerName;
      Renames[A.ProvenanceTarget] = ProvenanceName;
      OwnedAllocationIdentities.push_back(ProvenanceName);
      auto Pointer = std::make_unique<VVarExpr>(
          PointerName, VType::makePtr(A.SizeBytes), A.Loc, ProvenanceName);
      auto Provenance =
          std::make_unique<VVarExpr>(ProvenanceName, VType::makePtr(), A.Loc);

      auto NonzeroProvenance = std::make_unique<VBinOpExpr>(
          VBinOp::Ne, cloneVExpr(Provenance.get()),
          std::make_unique<VLiteralExpr>(0, VType::makePtr(), A.Loc),
          VType::makeBool(), A.Loc);
      emitPassive(P, PassiveStmt::Assume, std::move(NonzeroProvenance),
                  Active.get(), A.Loc);
      auto WasUsed = std::make_unique<VLoadExpr>(
          cloneVExpr(Provenance.get()), VType::makeBool(), A.Loc,
          Renames[VAllocationUsedHeapName]);
      emitPassive(P, PassiveStmt::Assume, makeNot(std::move(WasUsed), A.Loc),
                  Active.get(), A.Loc);
      updateHeap(P, Renames, VAllocationUsedHeapName,
                 cloneVExpr(Provenance.get()), makeBoolLiteral(true, A.Loc),
                 Active.get(), A.Loc);

      auto NonNull = std::make_unique<VBinOpExpr>(
          VBinOp::Ne, cloneVExpr(Pointer.get()),
          std::make_unique<VLiteralExpr>(0, VType::makePtr(), A.Loc),
          VType::makeBool(), A.Loc);
      emitPassive(P, PassiveStmt::Assume, std::move(NonNull), Active.get(),
                  A.Loc);
      if (A.AlignBytes > 1) {
        auto Remainder = std::make_unique<VBinOpExpr>(
            VBinOp::Rem, cloneVExpr(Pointer.get()),
            std::make_unique<VLiteralExpr>(std::to_string(A.AlignBytes),
                                           VType::makePtr(), A.Loc),
            VType::makePtr(), A.Loc);
        auto Aligned = makeEq(
            std::move(Remainder),
            std::make_unique<VLiteralExpr>(0, VType::makePtr(), A.Loc), A.Loc);
        emitPassive(P, PassiveStmt::Assume, std::move(Aligned), Active.get(),
                    A.Loc);
      }

      const std::string AllocationBefore = Renames[VAllocationHeapName];
      const std::string LivenessBefore = Renames[VLivenessHeapName];
      for (uint64_t Offset = 0; Offset < A.SizeBytes; ++Offset) {
        auto Address = addressOffset(Pointer.get(), Offset, A.Loc);
        auto Owner = std::make_unique<VLoadExpr>(
            std::move(Address), VType::makePtr(), A.Loc, AllocationBefore);
        auto Live = std::make_unique<VLoadExpr>(
            std::move(Owner), VType::makeBool(), A.Loc, LivenessBefore);
        emitPassive(P, PassiveStmt::Assume, makeNot(std::move(Live), A.Loc),
                    Active.get(), A.Loc);
      }

      for (uint64_t Offset = 0; Offset < A.SizeBytes; ++Offset)
        updateHeap(P, Renames, VAllocationHeapName,
                   addressOffset(Pointer.get(), Offset, A.Loc),
                   cloneVExpr(Provenance.get()), Active.get(), A.Loc);
      updateHeap(P, Renames, VAllocationBaseHeapName,
                 cloneVExpr(Provenance.get()), cloneVExpr(Pointer.get()),
                 Active.get(), A.Loc);
      updateHeap(P, Renames, VAllocationSizeHeapName,
                 cloneVExpr(Provenance.get()),
                 std::make_unique<VLiteralExpr>(std::to_string(A.SizeBytes),
                                                VType::makePtr(), A.Loc),
                 Active.get(), A.Loc);
      updateHeap(P, Renames, VAllocationAlignHeapName,
                 cloneVExpr(Provenance.get()),
                 std::make_unique<VLiteralExpr>(std::to_string(A.AlignBytes),
                                                VType::makePtr(), A.Loc),
                 Active.get(), A.Loc);
      updateHeap(P, Renames, VLivenessHeapName, cloneVExpr(Provenance.get()),
                 makeBoolLiteral(true, A.Loc), Active.get(), A.Loc);
      updateHeap(P, Renames, VInitializationHeapName, cloneVExpr(Pointer.get()),
                 makeBoolLiteral(Initializer != nullptr, A.Loc), Active.get(),
                 A.Loc);
      if (Initializer)
        updateHeap(P, Renames, VHeapName, cloneVExpr(Pointer.get()),
                   std::move(Initializer), Active.get(), A.Loc);
      break;
    }
    case VStmt::Free: {
      const auto &F = static_cast<const VFreeStmt &>(S);
      CloneCtx Ctx{Renames, OldState, false};
      auto Pointer = cloneExpr(F.Ptr.get(), Ctx);
      emitExprSafety(P, Pointer.get(), Active.get(), F.Loc, Renames);
      auto Provenance = pointerProvenance(Pointer.get());
      if (!Provenance) {
        emitPassive(P, PassiveStmt::Assert, makeBoolLiteral(false, F.Loc),
                    Active.get(), F.Loc);
        break;
      }
      auto IsNull = makeEq(
          cloneVExpr(Pointer.get()),
          std::make_unique<VLiteralExpr>(0, VType::makePtr(), F.Loc), F.Loc);
      auto Owner = std::make_unique<VLoadExpr>(cloneVExpr(Pointer.get()),
                                               VType::makePtr(), F.Loc,
                                               Renames[VAllocationHeapName]);
      auto HasIdentity =
          makeEq(cloneVExpr(Owner.get()), cloneVExpr(Provenance.get()), F.Loc);
      auto Base =
          std::make_unique<VLoadExpr>(cloneVExpr(Owner.get()), VType::makePtr(),
                                      F.Loc, Renames[VAllocationBaseHeapName]);
      auto IsBase = makeEq(std::move(Base), cloneVExpr(Pointer.get()), F.Loc);
      auto Live = std::make_unique<VLoadExpr>(cloneVExpr(Owner.get()),
                                              VType::makeBool(), F.Loc,
                                              Renames[VLivenessHeapName]);
      auto Deletable = makeOr(
          cloneVExpr(IsNull.get()),
          makeAnd(std::move(HasIdentity),
                  makeAnd(std::move(IsBase), cloneVExpr(Live.get()), F.Loc),
                  F.Loc),
          F.Loc);
      emitPassive(P, PassiveStmt::Assert, std::move(Deletable), Active.get(),
                  F.Loc);
      auto Owned = cloneVExpr(IsNull.get());
      for (const std::string &Identity : OwnedAllocationIdentities)
        Owned = makeOr(std::move(Owned),
                       makeEq(cloneVExpr(Provenance.get()),
                              std::make_unique<VVarExpr>(
                                  Identity, VType::makePtr(), F.Loc),
                              F.Loc),
                       F.Loc);
      emitPassive(P, PassiveStmt::Assert, std::move(Owned), Active.get(),
                  F.Loc);
      auto LivenessAfterDelete = std::make_unique<VConditionalExpr>(
          cloneVExpr(IsNull.get()), cloneVExpr(Live.get()),
          makeBoolLiteral(false, F.Loc), VType::makeBool(), F.Loc);
      updateHeap(P, Renames, VLivenessHeapName, std::move(Owner),
                 std::move(LivenessAfterDelete), Active.get(), F.Loc);
      break;
    }
    case VStmt::If: {
      const auto &I = static_cast<const VIfStmt &>(S);
      CloneCtx Ctx{Renames, OldState, false};
      auto Cond = cloneExpr(I.Cond.get(), Ctx);
      emitExprSafety(P, Cond.get(), Active.get(), I.Loc, Renames);
      auto EntryActive = cloneVExpr(Active.get());
      const auto EntryRenames = Renames;
      auto ThenRenames = Renames;
      auto ElseRenames = Renames;
      auto ThenActive =
          makeAnd(cloneVExpr(Active.get()), cloneVExpr(Cond.get()), I.Loc);
      auto ElseActive = makeAnd(cloneVExpr(Active.get()),
                                makeNot(cloneVExpr(Cond.get()), I.Loc), I.Loc);
      PassiveProgram ThenP;
      PassiveProgram ElseP;
      for (const auto &TS : I.Then)
        processStmt(*TS, ThenP, ThenRenames, ThenActive);
      for (const auto &ES : I.Else)
        processStmt(*ES, ElseP, ElseRenames, ElseActive);
      appendProgram(P, ThenP);
      appendProgram(P, ElseP);
      std::set<std::string> Changed;
      for (const auto &[Name, Ver] : ThenRenames)
        if (!ElseRenames.count(Name) || ElseRenames.at(Name) != Ver)
          Changed.insert(Name);
      for (const auto &[Name, Ver] : ElseRenames)
        if (!ThenRenames.count(Name) || ThenRenames.at(Name) != Ver)
          Changed.insert(Name);
      for (const std::string &Name : Changed) {
        VType Ty = typeForName(Name);
        auto branchValue = [&](const auto &BranchRenames) {
          if (auto It = BranchRenames.find(Name); It != BranchRenames.end())
            return It->second;
          if (auto It = EntryRenames.find(Name); It != EntryRenames.end())
            return It->second;
          return bump("__undefined_branch_value");
        };
        auto ThenVal =
            std::make_unique<VVarExpr>(branchValue(ThenRenames), Ty, I.Loc);
        auto ElseVal =
            std::make_unique<VVarExpr>(branchValue(ElseRenames), Ty, I.Loc);
        std::string Merged = bump(Name);
        Renames[Name] = Merged;
        auto MergeExpr = std::make_unique<VConditionalExpr>(
            cloneExpr(Cond.get(), Ctx), std::move(ThenVal), std::move(ElseVal),
            Ty, I.Loc);
        emitMathBridge(P, MergeExpr.get(), EntryActive.get(), I.Loc, true);
        emitPassive(P, PassiveStmt::Assume,
                    makeEq(std::make_unique<VVarExpr>(Merged, Ty, I.Loc),
                           std::move(MergeExpr), I.Loc),
                    EntryActive.get(), I.Loc);
      }
      Active = makeOr(std::move(ThenActive), std::move(ElseActive), I.Loc);
      break;
    }
    case VStmt::Return: {
      const auto &R = static_cast<const VReturnStmt &>(S);
      CloneCtx Ctx{Renames, OldState, false};
      ReturnGuards.push_back(cloneVExpr(Active.get()));
      if (!R.Value) {
        Active = makeBoolLiteral(false, R.Loc);
        break;
      }
      auto BoundReturn = cloneExpr(R.Value.get(), Ctx);
      emitExprSafety(P, BoundReturn.get(), Active.get(), R.Loc, Renames, true);
      const VExpr *RetVal = R.Value.get();
      while (RetVal && RetVal->K == VExpr::Cast)
        RetVal = static_cast<const VCastExpr *>(RetVal)->Inner.get();
      if (RetVal && RetVal->K == VExpr::Var) {
        const std::string &Src = static_cast<const VVarExpr *>(RetVal)->Name;
        FieldReturnCase Case{cloneVExpr(Active.get()), {}, R.Loc};
        for (const auto &[Field, Ty] : Fn.ReturnFields) {
          const std::string ResultField = "result." + Field;
          std::string SrcField = Src + "." + Field;
          std::string SrcVer = SrcField;
          if (auto It = Renames.find(SrcField); It != Renames.end())
            SrcVer = It->second;
          Case.Values[ResultField] =
              std::make_unique<VVarExpr>(SrcVer, Ty, R.Loc);
        }
        if (!Case.Values.empty()) {
          FieldReturnCases.push_back(std::move(Case));
          Active = makeBoolLiteral(false, R.Loc);
          break;
        }
      }
      ReturnCases.push_back(
          {cloneVExpr(Active.get()), std::move(BoundReturn), R.Loc});
      Active = makeBoolLiteral(false, R.Loc);
      break;
    }
    case VStmt::While: {
      const auto &W = static_cast<const VWhileStmt &>(S);
      bool HasReturn = false;
      for (const auto &Body : W.Body) {
        if (containsReturn(*Body)) {
          HasReturn = true;
          break;
        }
      }
      if (HasReturn) {
        emitPassive(P, PassiveStmt::Assert, makeBoolLiteral(false, W.Loc),
                    Active.get(), W.Loc);
        break;
      }
      CloneCtx EntryCtx{Renames, OldState, false};
      for (const auto &Inv : W.Invariants) {
        auto BoundInv = cloneExpr(Inv.get(), EntryCtx);
        emitExprSafety(P, BoundInv.get(), Active.get(), W.Loc, Renames);
        emitPassive(P, PassiveStmt::Assert, std::move(BoundInv), Active.get(),
                    W.Loc);
      }

      std::set<std::string> Modified;
      for (const auto &Body : W.Body)
        collectModified(*Body, Modified);
      for (const std::string &Name : Modified)
        if (Renames.count(Name))
          Renames[Name] = bump(Name);

      CloneCtx HeadCtx{Renames, OldState, false};
      for (const auto &Inv : W.Invariants) {
        auto BoundInv = cloneExpr(Inv.get(), HeadCtx);
        emitPassive(P, PassiveStmt::Assume, std::move(BoundInv), Active.get(),
                    W.Loc);
      }

      std::string ChoiceName = bump("__loop_choice");
      auto Choice =
          std::make_unique<VVarExpr>(ChoiceName, VType::makeBool(), W.Loc);
      auto IterationActive =
          makeAnd(cloneVExpr(Active.get()), cloneVExpr(Choice.get()), W.Loc);
      auto HeadCond = cloneExpr(W.Cond.get(), HeadCtx);
      emitExprSafety(P, HeadCond.get(), Active.get(), W.Loc, Renames);
      emitPassive(P, PassiveStmt::Assume, cloneVExpr(HeadCond.get()),
                  IterationActive.get(), W.Loc);

      std::vector<std::unique_ptr<VExpr>> OldDecreases;
      for (const auto &Decrease : W.Decreases) {
        auto Bound = cloneExpr(Decrease.get(), HeadCtx);
        emitExprSafety(P, Bound.get(), IterationActive.get(), W.Loc, Renames);
        OldDecreases.push_back(std::move(Bound));
      }
      if (!OldDecreases.empty())
        emitPassive(P, PassiveStmt::Assert,
                    buildTupleNonNegative(OldDecreases, W.Loc),
                    IterationActive.get(), W.Loc);

      auto BodyRenames = Renames;
      auto BodyActive = cloneVExpr(IterationActive.get());
      PassiveProgram BodyP;
      for (const auto &BS : W.Body)
        processStmt(*BS, BodyP, BodyRenames, BodyActive);
      appendProgram(P, BodyP);

      for (const auto &Inv : W.Invariants) {
        CloneCtx ACtx{BodyRenames, OldState, false};
        auto BoundInv = cloneExpr(Inv.get(), ACtx);
        emitExprSafety(P, BoundInv.get(), BodyActive.get(), W.Loc, BodyRenames);
        emitPassive(P, PassiveStmt::Assert, std::move(BoundInv),
                    BodyActive.get(), W.Loc);
      }

      if (!W.Decreases.empty()) {
        CloneCtx AfterCtx{BodyRenames, OldState, false};
        std::vector<std::unique_ptr<VExpr>> NewDecreases;
        for (const auto &Decrease : W.Decreases) {
          auto Bound = cloneExpr(Decrease.get(), AfterCtx);
          emitExprSafety(P, Bound.get(), BodyActive.get(), W.Loc, BodyRenames);
          NewDecreases.push_back(std::move(Bound));
        }
        emitPassive(P, PassiveStmt::Assert,
                    buildLexDecrease(NewDecreases, OldDecreases, W.Loc),
                    BodyActive.get(), W.Loc);
      }

      emitPassive(P, PassiveStmt::Assume, makeNot(std::move(Choice), W.Loc),
                  Active.get(), W.Loc);
      emitPassive(P, PassiveStmt::Assume, makeNot(std::move(HeadCond), W.Loc),
                  Active.get(), W.Loc);
      break;
    }
    case VStmt::GhostBlock: {
      const auto &G = static_cast<const VGhostBlockStmt &>(S);
      for (const auto &BS : G.Body)
        processStmt(*BS, P, Renames, Active);
      break;
    }
    case VStmt::ContractAssert: {
      const auto &A = static_cast<const VContractAssertStmt &>(S);
      CloneCtx Ctx{Renames, OldState, false};
      auto Cond = cloneExpr(A.Cond.get(), Ctx);
      emitExprSafety(P, Cond.get(), Active.get(), A.Loc, Renames);
      emitPassive(P, PassiveStmt::Assert, std::move(Cond), Active.get(), A.Loc);
      break;
    }
    case VStmt::RevealWithFuel:
    case VStmt::HideSpec:
    case VStmt::RevealSpec:
      break;
    case VStmt::Call: {
      PassiveProgram CallP;
      emitCallStmt(static_cast<const VCallStmt &>(S), CallP, Renames);
      for (auto &CallStmt : CallP.Stmts) {
        if (CallStmt->Cond)
          CallStmt->Cond = makeImplies(cloneVExpr(Active.get()),
                                       std::move(CallStmt->Cond), S.Loc);
        P.Stmts.push_back(std::move(CallStmt));
      }
      break;
    }
    case VStmt::Assert: {
      const auto &A = static_cast<const VAssertStmt &>(S);
      CloneCtx Ctx{Renames, OldState, false};
      auto Cond = cloneExpr(A.Cond.get(), Ctx);
      emitExprSafety(P, Cond.get(), Active.get(), A.Loc, Renames);
      emitPassive(P, PassiveStmt::Assert, std::move(Cond), Active.get(), A.Loc);
      break;
    }
    case VStmt::Assume: {
      const auto &A = static_cast<const VAssumeStmt &>(S);
      CloneCtx Ctx{Renames, OldState, false};
      auto Cond = cloneExpr(A.Cond.get(), Ctx);
      emitExprSafety(P, Cond.get(), Active.get(), A.Loc, Renames);
      emitPassive(P, PassiveStmt::Assume, std::move(Cond), Active.get(), A.Loc);
      break;
    }
    case VStmt::Seq:
      for (const auto &Nested : static_cast<const VSeqStmt &>(S).Stmts)
        processStmt(*Nested, P, Renames, Active);
      break;
    case VStmt::Havoc:
      Renames[static_cast<const VHavocStmt &>(S).Target] =
          bump(static_cast<const VHavocStmt &>(S).Target);
      break;
    }
  }
};

PassiveProgram Passivizer::run(const VFunction &Fn) {
  PassivizerImpl Impl(Fn, FnMap);
  return Impl.run();
}