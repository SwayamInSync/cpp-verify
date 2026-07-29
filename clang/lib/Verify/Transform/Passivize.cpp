//===--- Passivize.cpp ----------------------------------------------------===//
#include "Passivize.h"
#include "SpecInline.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/StringRef.h"
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
static std::unique_ptr<VExpr> cloneExprImpl(const VExpr *E,
                                            const CloneCtx &Ctx);

static const VVarExpr *directPointerRoot(const VExpr *E) {
  while (E && E->K == VExpr::Cast)
    E = static_cast<const VCastExpr *>(E)->Inner.get();
  if (E && E->K == VExpr::Var && E->Ty.Kind == VTypeKind::Ptr)
    return static_cast<const VVarExpr *>(E);
  if (!E || E->K != VExpr::BinOp)
    return nullptr;
  const auto *B = static_cast<const VBinOpExpr *>(E);
  if (B->Op != VBinOp::Add || B->Lhs->K != VExpr::Var ||
      B->Lhs->Ty.Kind != VTypeKind::Ptr || B->Rhs->Ty.Kind == VTypeKind::Ptr)
    return nullptr;
  return static_cast<const VVarExpr *>(B->Lhs.get());
}

static const VExpr *directPointerIndex(const VExpr *E, uint64_t Stride,
                                       bool &IsBase) {
  IsBase = false;
  while (E && E->K == VExpr::Cast)
    E = static_cast<const VCastExpr *>(E)->Inner.get();
  if (E && E->K == VExpr::Var) {
    IsBase = true;
    return nullptr;
  }
  if (!E || E->K != VExpr::BinOp)
    return nullptr;
  const auto *Add = static_cast<const VBinOpExpr *>(E);
  if (Add->Op != VBinOp::Add || Add->Lhs->K != VExpr::Var)
    return nullptr;
  const VExpr *Scaled = Add->Rhs.get();
  if (Stride != 1) {
    if (!Scaled || Scaled->K != VExpr::BinOp)
      return nullptr;
    const auto *Mul = static_cast<const VBinOpExpr *>(Scaled);
    if (Mul->Op != VBinOp::Mul || Mul->Rhs->K != VExpr::Literal ||
        static_cast<const VLiteralExpr *>(Mul->Rhs.get())->Value !=
            std::to_string(Stride))
      return nullptr;
    Scaled = Mul->Lhs.get();
  }
  if (!Scaled || Scaled->K != VExpr::Cast)
    return nullptr;
  const auto *Cast = static_cast<const VCastExpr *>(Scaled);
  if (Cast->FromTy.IntMode != VIntMode::Machine ||
      Cast->Ty.IntMode != VIntMode::Math)
    return nullptr;
  return Cast->Inner.get();
}

static const VBinOpExpr *loweredPointerDifferenceQuotient(const VCastExpr *C) {
  if (!C || C->Ty.IntMode != VIntMode::Machine || !C->Ty.isSignedInt() ||
      C->Ty.BitWidth == 0 || C->Inner->K != VExpr::BinOp)
    return nullptr;
  const auto *Quotient = static_cast<const VBinOpExpr *>(C->Inner.get());
  if (Quotient->Op != VBinOp::Div || Quotient->Lhs->K != VExpr::BinOp ||
      Quotient->Rhs->K != VExpr::Literal)
    return nullptr;
  const auto *Difference = static_cast<const VBinOpExpr *>(Quotient->Lhs.get());
  if (Difference->Op != VBinOp::Sub ||
      Difference->Lhs->Ty.Kind != VTypeKind::Ptr ||
      Difference->Rhs->Ty.Kind != VTypeKind::Ptr)
    return nullptr;
  return Quotient;
}

static bool directPointerDifferenceIndices(
    const VCastExpr *C, const VBinOpExpr *&Quotient, const VExpr *&LeftIndex,
    const VExpr *&RightIndex, bool &LeftIsBase, bool &RightIsBase) {
  Quotient = loweredPointerDifferenceQuotient(C);
  if (!Quotient)
    return false;
  const auto *Difference = static_cast<const VBinOpExpr *>(Quotient->Lhs.get());
  const auto *LeftRoot = directPointerRoot(Difference->Lhs.get());
  const auto *RightRoot = directPointerRoot(Difference->Rhs.get());
  if (!LeftRoot || !RightRoot || LeftRoot->Name != RightRoot->Name)
    return false;

  uint64_t Stride = 0;
  if (llvm::StringRef(
          static_cast<const VLiteralExpr *>(Quotient->Rhs.get())->Value)
          .getAsInteger(10, Stride) ||
      Stride == 0)
    return false;
  LeftIndex = directPointerIndex(Difference->Lhs.get(), Stride, LeftIsBase);
  RightIndex = directPointerIndex(Difference->Rhs.get(), Stride, RightIsBase);
  return (LeftIsBase || LeftIndex) && (RightIsBase || RightIndex);
}

static std::unique_ptr<VExpr>
normalizeDirectPointerDifference(const VCastExpr *C, const CloneCtx &Ctx) {
  const VBinOpExpr *B = nullptr;
  const VExpr *LeftIndex = nullptr;
  const VExpr *RightIndex = nullptr;
  bool LeftIsBase = false;
  bool RightIsBase = false;
  if (!directPointerDifferenceIndices(C, B, LeftIndex, RightIndex, LeftIsBase,
                                      RightIsBase))
    return nullptr;
  auto IsMachineIndex = [](const VExpr *Index) {
    return !Index || (Index->Ty.IntMode == VIntMode::Machine &&
                      (Index->Ty.Kind == VTypeKind::Int32 ||
                       Index->Ty.Kind == VTypeKind::Int64) &&
                      Index->Ty.BitWidth != 0);
  };
  if (!IsMachineIndex(LeftIndex) || !IsMachineIndex(RightIndex))
    return nullptr;

  auto ConvertIndex = [&](const VExpr *Index) -> std::unique_ptr<VExpr> {
    if (!Index)
      return std::make_unique<VLiteralExpr>(0, C->Ty, B->Loc);
    auto Value = cloneExpr(Index, Ctx);
    return std::make_unique<VCastExpr>(std::move(Value), Index->Ty, C->Ty,
                                       Index->Loc);
  };
  return std::make_unique<VBinOpExpr>(VBinOp::Sub, ConvertIndex(LeftIndex),
                                      ConvertIndex(RightIndex), C->Ty, B->Loc);
}

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
  auto Copy = cloneExprImpl(E, Ctx);
  if (Copy && E)
    Copy->EndLoc = E->EndLoc;
  return Copy;
}

static std::unique_ptr<VExpr> cloneExprImpl(const VExpr *E,
                                            const CloneCtx &Ctx) {
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
    if (auto Normalized = normalizeDirectPointerDifference(C, Ctx))
      return Normalized;
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
    return std::make_unique<VLoadExpr>(
        cloneExpr(L->Ptr.get(), Ctx), L->Ty, L->Loc, Heap,
        cloneExpr(L->AccessCondition.get(), Ctx));
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

std::unique_ptr<VExpr> verify::cloneAtEntryState(const VExpr *E) {
  static const std::map<std::string, std::string> Renames;
  static const std::map<std::string, std::unique_ptr<VExpr>> OldState;
  return cloneExpr(E, CloneCtx{Renames, OldState});
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

static std::unique_ptr<VExpr>
safetyForExpr(const VExpr *E, const FunctionMap *FnMap,
              const std::vector<VValidExtent> *ValidExtents = nullptr,
              const std::set<std::string> *PointerParams = nullptr);

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

static std::unique_ptr<VExpr> signedArithmeticSafety(const VBinOpExpr *B);

static std::unique_ptr<VExpr>
pointerDifferenceRepresentability(const VCastExpr *C) {
  const VBinOpExpr *Quotient = nullptr;
  const VExpr *LeftIndex = nullptr;
  const VExpr *RightIndex = nullptr;
  bool LeftIsBase = false;
  bool RightIsBase = false;
  if (directPointerDifferenceIndices(C, Quotient, LeftIndex, RightIndex,
                                     LeftIsBase, RightIsBase)) {
    if (!LeftIndex && !RightIndex)
      return makeBoolLiteral(true, C->Loc);
    const VType &IndexType = LeftIndex ? LeftIndex->Ty : RightIndex->Ty;
    const bool SameRepresentation =
        (!LeftIndex || (LeftIndex->Ty.Kind == IndexType.Kind &&
                        LeftIndex->Ty.IntMode == IndexType.IntMode &&
                        LeftIndex->Ty.IsSigned == IndexType.IsSigned &&
                        LeftIndex->Ty.BitWidth == IndexType.BitWidth)) &&
        (!RightIndex || (RightIndex->Ty.Kind == IndexType.Kind &&
                         RightIndex->Ty.IntMode == IndexType.IntMode &&
                         RightIndex->Ty.IsSigned == IndexType.IsSigned &&
                         RightIndex->Ty.BitWidth == IndexType.BitWidth));
    if (SameRepresentation && IndexType.IntMode == VIntMode::Machine &&
        isIntegerType(IndexType) && IndexType.BitWidth != 0) {
      if (IndexType.BitWidth < C->Ty.BitWidth)
        return makeBoolLiteral(true, C->Loc);
      if (IndexType.BitWidth == C->Ty.BitWidth) {
        auto IndexValue = [&](const VExpr *Index) -> std::unique_ptr<VExpr> {
          if (Index)
            return cloneVExpr(Index);
          return std::make_unique<VLiteralExpr>(0, IndexType, C->Loc);
        };
        if (IndexType.IsSigned) {
          auto Difference = std::make_unique<VBinOpExpr>(
              VBinOp::Sub, IndexValue(LeftIndex), IndexValue(RightIndex),
              IndexType, C->Loc);
          return signedArithmeticSafety(Difference.get());
        }

        auto Left = IndexValue(LeftIndex);
        auto Right = IndexValue(RightIndex);
        auto LeftAtLeastRight = std::make_unique<VBinOpExpr>(
            VBinOp::Ge, cloneVExpr(Left.get()), cloneVExpr(Right.get()),
            VType::makeBool(), C->Loc);
        auto ForwardDistance = std::make_unique<VBinOpExpr>(
            VBinOp::Sub, cloneVExpr(Left.get()), cloneVExpr(Right.get()),
            IndexType, C->Loc);
        auto ForwardFits = std::make_unique<VBinOpExpr>(
            VBinOp::Le, std::move(ForwardDistance),
            std::make_unique<VLiteralExpr>(signedLimit(C->Ty.BitWidth, false),
                                           IndexType, C->Loc),
            VType::makeBool(), C->Loc);

        llvm::APInt MinMagnitude =
            llvm::APInt::getOneBitSet(C->Ty.BitWidth, C->Ty.BitWidth - 1);
        llvm::SmallString<64> MinMagnitudeBuffer;
        MinMagnitude.toString(MinMagnitudeBuffer, 10, false);
        auto BackwardDistance = std::make_unique<VBinOpExpr>(
            VBinOp::Sub, std::move(Right), std::move(Left), IndexType, C->Loc);
        auto BackwardFits = std::make_unique<VBinOpExpr>(
            VBinOp::Le, std::move(BackwardDistance),
            std::make_unique<VLiteralExpr>(std::string(MinMagnitudeBuffer),
                                           IndexType, C->Loc),
            VType::makeBool(), C->Loc);
        auto ForwardOrder = cloneVExpr(LeftAtLeastRight.get());
        auto BackwardOrder = makeNot(std::move(LeftAtLeastRight), C->Loc);
        auto ForwardCase =
            makeAnd(std::move(ForwardOrder), std::move(ForwardFits), C->Loc);
        auto BackwardCase =
            makeAnd(std::move(BackwardOrder), std::move(BackwardFits), C->Loc);
        return makeOr(std::move(ForwardCase), std::move(BackwardCase), C->Loc);
      }
    }
  } else {
    Quotient = loweredPointerDifferenceQuotient(C);
  }
  if (!Quotient)
    return makeBoolLiteral(true, C ? C->Loc : SourceLocation());
  auto AtLeastMinimum = std::make_unique<VBinOpExpr>(
      VBinOp::Ge, cloneVExpr(Quotient),
      std::make_unique<VLiteralExpr>(signedLimit(C->Ty.BitWidth, true),
                                     Quotient->Ty, C->Loc),
      VType::makeBool(), C->Loc);
  auto AtMostMaximum = std::make_unique<VBinOpExpr>(
      VBinOp::Le, cloneVExpr(Quotient),
      std::make_unique<VLiteralExpr>(signedLimit(C->Ty.BitWidth, false),
                                     Quotient->Ty, C->Loc),
      VType::makeBool(), C->Loc);
  return makeAnd(std::move(AtLeastMinimum), std::move(AtMostMaximum), C->Loc);
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

static VType pointerOffsetType() {
  return VType::makeInt(VIntMode::Math, 64, true);
}

static bool sameIntegerRepresentation(const VType &L, const VType &R) {
  return (L.Kind == VTypeKind::Int32 || L.Kind == VTypeKind::Int64) &&
         L.Kind == R.Kind && L.IntMode == R.IntMode &&
         L.IsSigned == R.IsSigned && L.BitWidth == R.BitWidth;
}

static const VExpr *machineValueInsideMathCast(const VExpr *E) {
  if (!E || E->K != VExpr::Cast)
    return nullptr;
  const auto *Cast = static_cast<const VCastExpr *>(E);
  if (Cast->FromTy.IntMode != VIntMode::Machine ||
      Cast->Ty.IntMode != VIntMode::Math)
    return nullptr;
  return Cast->Inner.get();
}

static std::unique_ptr<VExpr> unscalePointerOffset(const VExpr *E,
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

static std::unique_ptr<VExpr>
directPointerElementOffset(const VExpr *E, const std::string &Base,
                           uint64_t PointeeSize, const VType &IndexType) {
  while (E && E->K == VExpr::Cast)
    E = static_cast<const VCastExpr *>(E)->Inner.get();
  if (E && E->K == VExpr::Var && static_cast<const VVarExpr *>(E)->Name == Base)
    return std::make_unique<VLiteralExpr>(0, IndexType, E->Loc);
  if (!E || E->K != VExpr::BinOp)
    return nullptr;
  const auto *Add = static_cast<const VBinOpExpr *>(E);
  if (Add->Op != VBinOp::Add || Add->Lhs->Ty.Kind != VTypeKind::Ptr ||
      Add->Rhs->Ty.Kind == VTypeKind::Ptr)
    return nullptr;
  const VExpr *PointerBase = pointerBase(Add->Lhs.get());
  if (!PointerBase || PointerBase->K != VExpr::Var ||
      static_cast<const VVarExpr *>(PointerBase)->Name != Base ||
      Add->Lhs->K != VExpr::Var)
    return nullptr;
  auto Offset = unscalePointerOffset(Add->Rhs.get(), PointeeSize);
  if (!Offset || !sameIntegerRepresentation(Offset->Ty, IndexType))
    return nullptr;
  return Offset;
}

static std::unique_ptr<VExpr> asPointerOffset(const VExpr *E) {
  if (!E)
    return nullptr;
  VType OffsetTy = pointerOffsetType();
  if (E->Ty.Kind != VTypeKind::Int32 && E->Ty.Kind != VTypeKind::Int64)
    return nullptr;
  return std::make_unique<VCastExpr>(cloneVExpr(E), E->Ty, OffsetTy, E->Loc);
}

static std::unique_ptr<VExpr> pointerByteOffset(const VExpr *E,
                                                const std::string &Base) {
  if (!E)
    return nullptr;
  while (E && E->K == VExpr::Cast)
    E = static_cast<const VCastExpr *>(E)->Inner.get();
  if (E->K == VExpr::Var) {
    if (static_cast<const VVarExpr *>(E)->Name != Base)
      return nullptr;
    return std::make_unique<VLiteralExpr>(0, pointerOffsetType(), E->Loc);
  }
  if (E->K != VExpr::BinOp)
    return nullptr;
  const auto *B = static_cast<const VBinOpExpr *>(E);
  if ((B->Op != VBinOp::Add && B->Op != VBinOp::Sub) ||
      B->Lhs->Ty.Kind != VTypeKind::Ptr || B->Rhs->Ty.Kind == VTypeKind::Ptr)
    return nullptr;
  auto BaseOffset = pointerByteOffset(B->Lhs.get(), Base);
  auto Delta = asPointerOffset(B->Rhs.get());
  if (!BaseOffset || !Delta)
    return nullptr;
  return std::make_unique<VBinOpExpr>(B->Op, std::move(BaseOffset),
                                      std::move(Delta), pointerOffsetType(),
                                      B->Loc);
}

static std::unique_ptr<VExpr>
scaledExtent(const VExpr *Length, uint64_t PointeeSize, SourceLocation Loc) {
  auto Count = asPointerOffset(Length);
  if (!Count || PointeeSize == 0)
    return nullptr;
  if (PointeeSize == 1)
    return Count;
  return std::make_unique<VBinOpExpr>(
      VBinOp::Mul, std::move(Count),
      std::make_unique<VLiteralExpr>(std::to_string(PointeeSize),
                                     pointerOffsetType(), Loc),
      pointerOffsetType(), Loc);
}

static std::unique_ptr<VExpr> pointerPositionSafety(
    const VExpr *Pointer, const std::vector<VValidExtent> *ValidExtents,
    const std::set<std::string> *PointerParams, SourceLocation Loc) {
  const VExpr *Base = pointerBase(Pointer);
  if (!Base || Base->K != VExpr::Var || Pointer->Ty.PointeeSizeBytes == 0)
    return makeBoolLiteral(false, Loc);
  const auto *BaseVar = static_cast<const VVarExpr *>(Base);

  const VValidExtent *MatchingExtent = nullptr;
  if (ValidExtents)
    for (const VValidExtent &Extent : *ValidExtents)
      if (Extent.Base == BaseVar->Name &&
          Extent.PointerType.PointeeSizeBytes == Pointer->Ty.PointeeSizeBytes) {
        MatchingExtent = &Extent;
        break;
      }
  if (MatchingExtent) {
    auto ElementOffset = directPointerElementOffset(
        Pointer, BaseVar->Name, Pointer->Ty.PointeeSizeBytes,
        MatchingExtent->Length->Ty);
    if (ElementOffset) {
      auto NonNegative = std::make_unique<VBinOpExpr>(
          VBinOp::Ge, cloneVExpr(ElementOffset.get()),
          std::make_unique<VLiteralExpr>(0, ElementOffset->Ty, Loc),
          VType::makeBool(), Loc);
      auto WithinExtent = std::make_unique<VBinOpExpr>(
          VBinOp::Le, std::move(ElementOffset),
          cloneVExpr(MatchingExtent->Length.get()), VType::makeBool(), Loc);
      return makeAnd(std::move(NonNegative), std::move(WithinExtent), Loc);
    }
  }

  const bool IsDynamic = hasPointerProvenance(Pointer);
  const bool IsDirectParameter =
      PointerParams && PointerParams->count(BaseVar->Name);
  if (!MatchingExtent && (IsDynamic || IsDirectParameter)) {
    const VExpr *Unwrapped = Pointer;
    while (Unwrapped && Unwrapped->K == VExpr::Cast)
      Unwrapped = static_cast<const VCastExpr *>(Unwrapped)->Inner.get();
    if (Unwrapped && Unwrapped->K == VExpr::Var)
      return makeBoolLiteral(true, Loc);
    if (Unwrapped && Unwrapped->K == VExpr::BinOp) {
      const auto *Add = static_cast<const VBinOpExpr *>(Unwrapped);
      if (Add->Op == VBinOp::Add && Add->Lhs->K == VExpr::Var &&
          static_cast<const VVarExpr *>(Add->Lhs.get())->Name ==
              BaseVar->Name) {
        auto ElementOffset =
            unscalePointerOffset(Add->Rhs.get(), Pointer->Ty.PointeeSizeBytes);
        if (ElementOffset) {
          VType ElementOffsetType = ElementOffset->Ty;
          auto NonNegative = std::make_unique<VBinOpExpr>(
              VBinOp::Ge, cloneVExpr(ElementOffset.get()),
              std::make_unique<VLiteralExpr>(0, ElementOffsetType, Loc),
              VType::makeBool(), Loc);
          auto OnePast = std::make_unique<VBinOpExpr>(
              VBinOp::Le, std::move(ElementOffset),
              std::make_unique<VLiteralExpr>(1, ElementOffsetType, Loc),
              VType::makeBool(), Loc);
          return makeAnd(std::move(NonNegative), std::move(OnePast), Loc);
        }
      }
    }
  }

  auto Offset = pointerByteOffset(Pointer, BaseVar->Name);
  if (!Offset)
    return makeBoolLiteral(false, Loc);

  std::unique_ptr<VExpr> Limit;
  if (MatchingExtent)
    Limit = scaledExtent(MatchingExtent->Length.get(),
                         MatchingExtent->PointerType.PointeeSizeBytes, Loc);
  if (!Limit && (IsDynamic || IsDirectParameter))
    Limit = std::make_unique<VLiteralExpr>(
        std::to_string(Pointer->Ty.PointeeSizeBytes), pointerOffsetType(), Loc);
  if (!Limit)
    return makeBoolLiteral(false, Loc);

  auto NonNegative = std::make_unique<VBinOpExpr>(
      VBinOp::Ge, cloneVExpr(Offset.get()),
      std::make_unique<VLiteralExpr>(0, pointerOffsetType(), Loc),
      VType::makeBool(), Loc);
  auto WithinExtent = std::make_unique<VBinOpExpr>(
      VBinOp::Le, std::move(Offset), std::move(Limit), VType::makeBool(), Loc);
  return makeAnd(std::move(NonNegative), std::move(WithinExtent), Loc);
}

static std::unique_ptr<VExpr> sliceContainment(
    const VExpr *Pointer, const VExpr *Length, uint64_t PointeeSize,
    const std::vector<VValidExtent> &CallerExtents, SourceLocation Loc) {
  const VExpr *Base = pointerBase(Pointer);
  if (!Base || Base->K != VExpr::Var || PointeeSize == 0)
    return makeBoolLiteral(false, Loc);
  const std::string &BaseName = static_cast<const VVarExpr *>(Base)->Name;
  auto Offset = pointerByteOffset(Pointer, BaseName);
  auto SliceBytes = scaledExtent(Length, PointeeSize, Loc);
  if (!Offset || !SliceBytes)
    return makeBoolLiteral(false, Loc);

  std::unique_ptr<VExpr> Contained = makeBoolLiteral(false, Loc);
  for (const VValidExtent &Outer : CallerExtents) {
    if (Outer.Base != BaseName ||
        Outer.PointerType.PointeeSizeBytes != PointeeSize)
      continue;
    if (sameIntegerRepresentation(Length->Ty, Outer.Length->Ty)) {
      auto ElementOffset = directPointerElementOffset(
          Pointer, BaseName, PointeeSize, Outer.Length->Ty);
      if (ElementOffset) {
        auto OffsetNonNegative = std::make_unique<VBinOpExpr>(
            VBinOp::Ge, cloneVExpr(ElementOffset.get()),
            std::make_unique<VLiteralExpr>(0, ElementOffset->Ty, Loc),
            VType::makeBool(), Loc);
        auto OffsetWithin = std::make_unique<VBinOpExpr>(
            VBinOp::Le, cloneVExpr(ElementOffset.get()),
            cloneVExpr(Outer.Length.get()), VType::makeBool(), Loc);
        auto LengthNonNegative = std::make_unique<VBinOpExpr>(
            VBinOp::Ge, cloneVExpr(Length),
            std::make_unique<VLiteralExpr>(0, Length->Ty, Loc),
            VType::makeBool(), Loc);
        auto Remaining = std::make_unique<VBinOpExpr>(
            VBinOp::Sub, cloneVExpr(Outer.Length.get()),
            std::move(ElementOffset), Outer.Length->Ty, Loc);
        auto LengthWithin = std::make_unique<VBinOpExpr>(
            VBinOp::Le, cloneVExpr(Length), std::move(Remaining),
            VType::makeBool(), Loc);
        auto ThisExtent =
            makeAnd(std::move(OffsetNonNegative), std::move(OffsetWithin), Loc);
        ThisExtent =
            makeAnd(std::move(ThisExtent), std::move(LengthNonNegative), Loc);
        ThisExtent =
            makeAnd(std::move(ThisExtent), std::move(LengthWithin), Loc);
        Contained = makeOr(std::move(Contained), std::move(ThisExtent), Loc);
        continue;
      }
    }
    auto OuterBytes = scaledExtent(Outer.Length.get(), PointeeSize, Loc);
    if (!OuterBytes)
      continue;
    auto OffsetNonNegative = std::make_unique<VBinOpExpr>(
        VBinOp::Ge, cloneVExpr(Offset.get()),
        std::make_unique<VLiteralExpr>(0, pointerOffsetType(), Loc),
        VType::makeBool(), Loc);
    auto LengthValue = asPointerOffset(Length);
    if (!LengthValue)
      continue;
    auto LengthNonNegative = std::make_unique<VBinOpExpr>(
        VBinOp::Ge, std::move(LengthValue),
        std::make_unique<VLiteralExpr>(0, pointerOffsetType(), Loc),
        VType::makeBool(), Loc);
    auto End = std::make_unique<VBinOpExpr>(
        VBinOp::Add, cloneVExpr(Offset.get()), cloneVExpr(SliceBytes.get()),
        pointerOffsetType(), Loc);
    auto EndsWithin = std::make_unique<VBinOpExpr>(VBinOp::Le, std::move(End),
                                                   std::move(OuterBytes),
                                                   VType::makeBool(), Loc);
    auto ThisExtent = makeAnd(std::move(OffsetNonNegative),
                              std::move(LengthNonNegative), Loc);
    ThisExtent = makeAnd(std::move(ThisExtent), std::move(EndsWithin), Loc);
    Contained = makeOr(std::move(Contained), std::move(ThisExtent), Loc);
  }
  return Contained;
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

static bool pointerUsePreservesParam(const VExpr *E, const std::string &Param) {
  if (!E || !referencesVar(E, Param))
    return true;
  while (E && E->K == VExpr::Cast)
    E = static_cast<const VCastExpr *>(E)->Inner.get();
  if (isDirectPointerParam(E, Param))
    return true;
  if (E && E->K == VExpr::Conditional) {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    return pointerUsePreservesParam(C->Then.get(), Param) &&
           pointerUsePreservesParam(C->Else.get(), Param);
  }
  return false;
}

static bool isLoweredPointerDifference(const VExpr *E) {
  if (!E || E->K != VExpr::BinOp)
    return false;
  const auto *B = static_cast<const VBinOpExpr *>(E);
  if (B->Op == VBinOp::Sub && B->Lhs->Ty.Kind == VTypeKind::Ptr &&
      B->Rhs->Ty.Kind == VTypeKind::Ptr)
    return true;
  return B->Op == VBinOp::Div && isLoweredPointerDifference(B->Lhs.get()) &&
         B->Rhs->K == VExpr::Literal;
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
    if (isLoweredPointerDifference(B))
      return true;
    if ((B->Lhs->Ty.Kind == VTypeKind::Ptr ||
         B->Rhs->Ty.Kind == VTypeKind::Ptr) &&
        referencesVar(B, Param) && B->Op != VBinOp::Eq && B->Op != VBinOp::Ne &&
        !isLoweredPointerDifference(B))
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
        C->Ty.Kind != VTypeKind::Bool &&
        !isLoweredPointerDifference(C->Inner.get()))
      return false;
    return scalarDynamicExprSafe(C->Inner.get(), Param);
  }
  case VExpr::Load: {
    const auto *L = static_cast<const VLoadExpr *>(E);
    if (referencesVar(L->Ptr.get(), Param) &&
        !isDirectPointerParam(L->Ptr.get(), Param))
      return false;
    return scalarDynamicExprSafe(L->Ptr.get(), Param) &&
           scalarDynamicExprSafe(L->AccessCondition.get(), Param);
  }
  case VExpr::Old:
    return scalarDynamicExprSafe(static_cast<const VOldExpr *>(E)->Inner.get(),
                                 Param);
  case VExpr::Conditional: {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    if (C->Ty.Kind == VTypeKind::Ptr && !pointerUsePreservesParam(C, Param))
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
  case VExpr::SpecCall: {
    const auto *C = static_cast<const VSpecCallExpr *>(E);
    for (const auto &Arg : C->Args) {
      if (Arg->Ty.Kind == VTypeKind::Ptr && referencesVar(Arg.get(), Param))
        return false;
      if (!scalarDynamicExprSafe(Arg.get(), Param))
        return false;
    }
    return true;
  }
  case VExpr::OverflowCheck: {
    const auto *O = static_cast<const VOverflowCheckExpr *>(E);
    return scalarDynamicExprSafe(O->Lhs.get(), Param) &&
           scalarDynamicExprSafe(O->Rhs.get(), Param);
  }
  }
  return false;
}

static bool referencesAnyAlias(const VExpr *E,
                               const std::set<std::string> &Aliases) {
  return std::any_of(
      Aliases.begin(), Aliases.end(),
      [&](const std::string &Alias) { return referencesVar(E, Alias); });
}

static bool isDirectPointerAlias(const VExpr *E,
                                 const std::set<std::string> &Aliases) {
  return std::any_of(
      Aliases.begin(), Aliases.end(),
      [&](const std::string &Alias) { return isDirectPointerParam(E, Alias); });
}

static bool scalarDynamicExprSafe(const VExpr *E,
                                  const std::set<std::string> &Aliases) {
  return std::all_of(Aliases.begin(), Aliases.end(),
                     [&](const std::string &Alias) {
                       return scalarDynamicExprSafe(E, Alias);
                     });
}

static bool pointerUsePreservesAliases(const VExpr *E,
                                       const std::set<std::string> &Aliases) {
  return std::all_of(Aliases.begin(), Aliases.end(),
                     [&](const std::string &Alias) {
                       return pointerUsePreservesParam(E, Alias);
                     });
}

static bool scalarDynamicCalleeSafe(
    const VFunction &Fn, const std::string &Param, const FunctionMap &FnMap,
    std::set<std::pair<std::string, std::string>> &ActiveScans);

static bool scalarDynamicStmtSafe(
    const VStmt &S, const std::string &Param, const FunctionMap &FnMap,
    std::set<std::pair<std::string, std::string>> &ActiveScans,
    std::set<std::string> &Aliases) {
  switch (S.K) {
  case VStmt::Assign: {
    const auto &A = static_cast<const VAssignStmt &>(S);
    if (A.IsReferenceBinding && A.Value->Ty.Kind == VTypeKind::Ptr &&
        isDirectPointerAlias(A.Value.get(), Aliases)) {
      if (Aliases.count(A.Target))
        return false;
      Aliases.insert(A.Target);
      return scalarDynamicExprSafe(A.Value.get(), Aliases);
    }
    return !Aliases.count(A.Target) &&
           !(A.Value->Ty.Kind == VTypeKind::Ptr &&
             referencesAnyAlias(A.Value.get(), Aliases)) &&
           scalarDynamicExprSafe(A.Value.get(), Aliases);
  }
  case VStmt::Store: {
    const auto &St = static_cast<const VStoreStmt &>(S);
    return (!referencesAnyAlias(St.Ptr.get(), Aliases) ||
            isDirectPointerAlias(St.Ptr.get(), Aliases)) &&
           !(St.Value->Ty.Kind == VTypeKind::Ptr &&
             referencesAnyAlias(St.Value.get(), Aliases)) &&
           scalarDynamicExprSafe(St.Ptr.get(), Aliases) &&
           scalarDynamicExprSafe(St.Value.get(), Aliases) &&
           scalarDynamicExprSafe(St.AccessCondition.get(), Aliases);
  }
  case VStmt::Allocate: {
    const auto &A = static_cast<const VAllocateStmt &>(S);
    return !Aliases.count(A.Target) &&
           scalarDynamicExprSafe(A.Initializer.get(), Aliases);
  }
  case VStmt::EndLifetime:
    return true;
  case VStmt::Free:
    return !referencesAnyAlias(static_cast<const VFreeStmt &>(S).Ptr.get(),
                               Aliases);
  case VStmt::If: {
    const auto &I = static_cast<const VIfStmt &>(S);
    if (!scalarDynamicExprSafe(I.Cond.get(), Aliases))
      return false;
    for (const auto &Nested : I.Then)
      if (!scalarDynamicStmtSafe(*Nested, Param, FnMap, ActiveScans, Aliases))
        return false;
    for (const auto &Nested : I.Else)
      if (!scalarDynamicStmtSafe(*Nested, Param, FnMap, ActiveScans, Aliases))
        return false;
    return true;
  }
  case VStmt::While: {
    const auto &W = static_cast<const VWhileStmt &>(S);
    if (!scalarDynamicExprSafe(W.Cond.get(), Aliases))
      return false;
    for (const auto &E : W.Invariants)
      if (!scalarDynamicExprSafe(E.get(), Aliases))
        return false;
    for (const auto &E : W.Decreases)
      if (!scalarDynamicExprSafe(E.get(), Aliases))
        return false;
    for (const auto &Nested : W.Body)
      if (!scalarDynamicStmtSafe(*Nested, Param, FnMap, ActiveScans, Aliases))
        return false;
    return true;
  }
  case VStmt::Call: {
    const auto &C = static_cast<const VCallStmt &>(S);
    auto CalleeIt = FnMap.find(C.CalleeIdentity);
    if (CalleeIt == FnMap.end())
      return false;
    const VFunction &Callee = *CalleeIt->second;
    if (Callee.IsSpec || Callee.IsProof || Callee.IsExternalContract ||
        Callee.UsesDynamicStorage)
      return false;
    for (unsigned I = 0; I < C.Args.size(); ++I) {
      const VExpr *Arg = C.Args[I].get();
      if (!scalarDynamicExprSafe(Arg, Aliases))
        return false;
      if (!referencesAnyAlias(Arg, Aliases) || Arg->Ty.Kind != VTypeKind::Ptr)
        continue;
      if (!isDirectPointerAlias(Arg, Aliases) || I >= Callee.Params.size() ||
          Callee.Params[I].second.Kind != VTypeKind::Ptr ||
          !scalarDynamicCalleeSafe(Callee, Callee.Params[I].first, FnMap,
                                   ActiveScans))
        return false;
    }
    return Callee.ReturnType.Kind != VTypeKind::Ptr;
  }
  case VStmt::Assert:
    return scalarDynamicExprSafe(static_cast<const VAssertStmt &>(S).Cond.get(),
                                 Aliases);
  case VStmt::Assume:
    return scalarDynamicExprSafe(static_cast<const VAssumeStmt &>(S).Cond.get(),
                                 Aliases);
  case VStmt::Return: {
    const auto &R = static_cast<const VReturnStmt &>(S);
    return (!R.Value || R.Value->Ty.Kind != VTypeKind::Ptr ||
            pointerUsePreservesAliases(R.Value.get(), Aliases)) &&
           scalarDynamicExprSafe(R.Value.get(), Aliases);
  }
  case VStmt::Seq:
    for (const auto &Nested : static_cast<const VSeqStmt &>(S).Stmts)
      if (!scalarDynamicStmtSafe(*Nested, Param, FnMap, ActiveScans, Aliases))
        return false;
    return true;
  case VStmt::GhostBlock:
    return false;
  case VStmt::ContractAssert:
    return scalarDynamicExprSafe(
        static_cast<const VContractAssertStmt &>(S).Cond.get(), Aliases);
  case VStmt::Havoc:
    return !Aliases.count(static_cast<const VHavocStmt &>(S).Target);
  case VStmt::RevealWithFuel:
  case VStmt::HideSpec:
  case VStmt::RevealSpec:
    return true;
  }
  return false;
}

static bool scalarDynamicCalleeSafe(
    const VFunction &Fn, const std::string &Param, const FunctionMap &FnMap,
    std::set<std::pair<std::string, std::string>> &ActiveScans) {
  const auto Key = std::make_pair(Fn.Identity, Param);
  if (!ActiveScans.insert(Key).second)
    return false;
  bool Safe = true;
  std::set<std::string> Aliases = {Param};
  for (unsigned I = 0;
       I < Fn.ExplicitPreconditionCount && I < Fn.Preconditions.size(); ++I)
    if (!scalarDynamicExprSafe(Fn.Preconditions[I].get(), Aliases))
      Safe = false;
  for (const auto &E : Fn.Postconditions)
    if (!scalarDynamicExprSafe(E.get(), Aliases))
      Safe = false;
  for (const auto &E : Fn.Modifies)
    if (!scalarDynamicExprSafe(E.get(), Aliases))
      Safe = false;
  for (const auto &E : Fn.Recommends)
    if (!scalarDynamicExprSafe(E.get(), Aliases))
      Safe = false;
  for (const auto &E : Fn.Decreases)
    if (!scalarDynamicExprSafe(E.get(), Aliases))
      Safe = false;
  for (const auto &S : Fn.Body)
    if (!scalarDynamicStmtSafe(*S, Param, FnMap, ActiveScans, Aliases))
      Safe = false;
  ActiveScans.erase(Key);
  return Safe;
}

static bool pointerResultComesFrom(const VExpr *E,
                                   const std::set<std::string> &Params) {
  if (!E)
    return false;
  while (E && E->K == VExpr::Cast)
    E = static_cast<const VCastExpr *>(E)->Inner.get();
  if (E->K == VExpr::Literal) {
    const auto *L = static_cast<const VLiteralExpr *>(E);
    return E->Ty.Kind == VTypeKind::Ptr && L->Value == "0";
  }
  if (E->K == VExpr::Var)
    return Params.count(static_cast<const VVarExpr *>(E)->Name) != 0;
  if (E->K == VExpr::Conditional) {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    return pointerResultComesFrom(C->Then.get(), Params) &&
           pointerResultComesFrom(C->Else.get(), Params);
  }
  return false;
}

static bool pointerReturnsComeFrom(const VStmt &S,
                                   const std::set<std::string> &Params) {
  switch (S.K) {
  case VStmt::Return: {
    const auto &R = static_cast<const VReturnStmt &>(S);
    return !R.Value || R.Value->Ty.Kind != VTypeKind::Ptr ||
           pointerResultComesFrom(R.Value.get(), Params);
  }
  case VStmt::If: {
    const auto &I = static_cast<const VIfStmt &>(S);
    for (const auto &Nested : I.Then)
      if (!pointerReturnsComeFrom(*Nested, Params))
        return false;
    for (const auto &Nested : I.Else)
      if (!pointerReturnsComeFrom(*Nested, Params))
        return false;
    return true;
  }
  case VStmt::While:
    for (const auto &Nested : static_cast<const VWhileStmt &>(S).Body)
      if (!pointerReturnsComeFrom(*Nested, Params))
        return false;
    return true;
  case VStmt::Seq:
    for (const auto &Nested : static_cast<const VSeqStmt &>(S).Stmts)
      if (!pointerReturnsComeFrom(*Nested, Params))
        return false;
    return true;
  case VStmt::GhostBlock:
    return false;
  default:
    return true;
  }
}

static bool pointerReturnsComeFrom(const VFunction &Fn,
                                   const std::set<std::string> &Params) {
  for (const auto &S : Fn.Body)
    if (!pointerReturnsComeFrom(*S, Params))
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

static std::unique_ptr<VExpr> samePointerDifferenceOrigin(const VExpr *L,
                                                          const VExpr *R,
                                                          SourceLocation Loc) {
  auto LProvenance = pointerProvenance(L);
  auto RProvenance = pointerProvenance(R);
  if (LProvenance && RProvenance)
    return makeEq(std::move(LProvenance), std::move(RProvenance), Loc);
  if (LProvenance || RProvenance)
    return makeBoolLiteral(false, Loc);

  const VExpr *LBase = pointerBase(L);
  const VExpr *RBase = pointerBase(R);
  if (!LBase || !RBase || LBase->K != VExpr::Var || RBase->K != VExpr::Var)
    return makeBoolLiteral(false, Loc);
  const auto *LVar = static_cast<const VVarExpr *>(LBase);
  const auto *RVar = static_cast<const VVarExpr *>(RBase);
  return makeBoolLiteral(LVar->Name == RVar->Name, Loc);
}

static bool isRegionFootprint(const VExpr *E,
                              const std::set<std::string> &ReferenceParams) {
  if (!E || E->K != VExpr::Load)
    return true;
  const VExpr *Ptr = static_cast<const VLoadExpr *>(E)->Ptr.get();
  while (Ptr && Ptr->K == VExpr::Cast)
    Ptr = static_cast<const VCastExpr *>(Ptr)->Inner.get();
  if (Ptr && Ptr->K == VExpr::Var &&
      ReferenceParams.count(static_cast<const VVarExpr *>(Ptr)->Name))
    return false;
  return !Ptr || Ptr->K == VExpr::Var;
}

static bool hasUnboundedExtentWrite(const VFunction &Fn,
                                    const std::string &Base) {
  for (const auto &Modify : Fn.Modifies) {
    if (!Modify || Modify->K != VExpr::Load ||
        !isRegionFootprint(Modify.get(), Fn.ReferenceParams))
      continue;
    const VExpr *Ptr =
        pointerBase(static_cast<const VLoadExpr *>(Modify.get())->Ptr.get());
    if (Ptr && Ptr->K == VExpr::Var &&
        static_cast<const VVarExpr *>(Ptr)->Name == Base)
      return true;
  }
  return false;
}

static bool functionMayWriteHeap(const VFunction &Fn, const FunctionMap &FnMap,
                                 std::set<std::string> &Active);

static bool stmtMayWriteHeap(const VStmt &S, const FunctionMap &FnMap,
                             std::set<std::string> &Active) {
  switch (S.K) {
  case VStmt::Store:
  case VStmt::Allocate:
  case VStmt::Free:
    return true;
  case VStmt::Call: {
    const auto &Call = static_cast<const VCallStmt &>(S);
    auto It = FnMap.find(Call.CalleeIdentity);
    if (It == FnMap.end())
      return true;
    return functionMayWriteHeap(*It->second, FnMap, Active);
  }
  case VStmt::If: {
    const auto &If = static_cast<const VIfStmt &>(S);
    for (const auto &Nested : If.Then)
      if (stmtMayWriteHeap(*Nested, FnMap, Active))
        return true;
    for (const auto &Nested : If.Else)
      if (stmtMayWriteHeap(*Nested, FnMap, Active))
        return true;
    return false;
  }
  case VStmt::While:
    for (const auto &Nested : static_cast<const VWhileStmt &>(S).Body)
      if (stmtMayWriteHeap(*Nested, FnMap, Active))
        return true;
    return false;
  case VStmt::Seq:
    for (const auto &Nested : static_cast<const VSeqStmt &>(S).Stmts)
      if (stmtMayWriteHeap(*Nested, FnMap, Active))
        return true;
    return false;
  case VStmt::GhostBlock:
    for (const auto &Nested : static_cast<const VGhostBlockStmt &>(S).Body)
      if (stmtMayWriteHeap(*Nested, FnMap, Active))
        return true;
    return false;
  case VStmt::Assign:
  case VStmt::EndLifetime:
  case VStmt::Assert:
  case VStmt::Assume:
  case VStmt::Return:
  case VStmt::Havoc:
  case VStmt::RevealWithFuel:
  case VStmt::HideSpec:
  case VStmt::RevealSpec:
  case VStmt::ContractAssert:
    return false;
  }
  return true;
}

static bool functionMayWriteHeap(const VFunction &Fn, const FunctionMap &FnMap,
                                 std::set<std::string> &Active) {
  if (Fn.IsProof || Fn.IsSpec)
    return false;
  if (!Fn.Modifies.empty() || Fn.IsExternalContract || Fn.UsesDynamicStorage ||
      Fn.FreshOwnedReturn)
    return true;
  if (!Active.insert(Fn.Identity).second)
    return true;
  bool Writes = false;
  for (const auto &S : Fn.Body)
    if (stmtMayWriteHeap(*S, FnMap, Active)) {
      Writes = true;
      break;
    }
  Active.erase(Fn.Identity);
  return Writes;
}

static bool hasImplicitHeapEffect(const VFunction &Fn,
                                  const FunctionMap &FnMap) {
  if (Fn.IsProof || !Fn.Modifies.empty())
    return false;
  bool HasPointerParam = false;
  for (const auto &Param : Fn.Params)
    HasPointerParam |= Param.second.Kind == VTypeKind::Ptr;
  if (!HasPointerParam)
    return false;
  std::set<std::string> Active;
  return functionMayWriteHeap(Fn, FnMap, Active);
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

static std::unique_ptr<VExpr> exactPointerSafety(const VExpr *Ptr,
                                                 SourceLocation Loc) {
  auto NonNull = std::make_unique<VBinOpExpr>(
      VBinOp::Ne, cloneVExpr(Ptr),
      std::make_unique<VLiteralExpr>(0, VType::makePtr(), Loc),
      VType::makeBool(), Loc);
  auto Valid = std::make_unique<VUnaryOpExpr>(
      VUnaryOp::ValidPtr, cloneVExpr(Ptr), VType::makeBool(), Loc);
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

static std::unique_ptr<VExpr>
safetyForExpr(const VExpr *E, const FunctionMap *FnMap,
              const std::vector<VValidExtent> *ValidExtents,
              const std::set<std::string> *PointerParams) {
  if (!E)
    return makeBoolLiteral(false, SourceLocation());
  switch (E->K) {
  case VExpr::Literal:
  case VExpr::Var:
  case VExpr::Result:
    return makeBoolLiteral(true, E->Loc);
  case VExpr::BinOp: {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    auto Left = safetyForExpr(B->Lhs.get(), FnMap, ValidExtents, PointerParams);
    auto Right =
        safetyForExpr(B->Rhs.get(), FnMap, ValidExtents, PointerParams);
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
    if (B->Op == VBinOp::Sub && B->Lhs->Ty.Kind == VTypeKind::Ptr &&
        B->Rhs->Ty.Kind == VTypeKind::Ptr) {
      const VExpr *LeftBase = pointerBase(B->Lhs.get());
      const VExpr *RightBase = pointerBase(B->Rhs.get());
      auto Defined = makeAnd(nonNullSafety(LeftBase, B->Loc),
                             nonNullSafety(RightBase, B->Loc), B->Loc);
      Defined = makeAnd(
          std::move(Defined),
          samePointerDifferenceOrigin(B->Lhs.get(), B->Rhs.get(), B->Loc),
          B->Loc);
      Defined = makeAnd(std::move(Defined),
                        pointerPositionSafety(B->Lhs.get(), ValidExtents,
                                              PointerParams, B->Loc),
                        B->Loc);
      Defined = makeAnd(std::move(Defined),
                        pointerPositionSafety(B->Rhs.get(), ValidExtents,
                                              PointerParams, B->Loc),
                        B->Loc);
      Safe = combineSafety(std::move(Safe), std::move(Defined), B->Loc);
    }
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
    auto Safe =
        safetyForExpr(U->Operand.get(), FnMap, ValidExtents, PointerParams);
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
  case VExpr::Cast: {
    const auto *C = static_cast<const VCastExpr *>(E);
    auto Safe =
        safetyForExpr(C->Inner.get(), FnMap, ValidExtents, PointerParams);
    if (loweredPointerDifferenceQuotient(C))
      Safe = combineSafety(std::move(Safe),
                           pointerDifferenceRepresentability(C), C->Loc);
    return Safe;
  }
  case VExpr::Load: {
    const auto *L = static_cast<const VLoadExpr *>(E);
    auto Safe = combineSafety(
        safetyForExpr(L->Ptr.get(), FnMap, ValidExtents, PointerParams),
        nonNullSafety(L->Ptr.get(), L->Loc), L->Loc);
    Safe = combineSafety(std::move(Safe),
                         initializedSafety(L->Ptr.get(), L->Loc), L->Loc);
    if (L->AccessCondition)
      Safe = combineSafety(std::move(Safe),
                           cloneVExpr(L->AccessCondition.get()), L->Loc);
    return Safe;
  }
  case VExpr::Old: {
    auto Safety = safetyForExpr(static_cast<const VOldExpr *>(E)->Inner.get(),
                                FnMap, ValidExtents, PointerParams);
    return std::make_unique<VOldExpr>(std::move(Safety), VType::makeBool(),
                                      E->Loc);
  }
  case VExpr::Conditional: {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    auto Safe =
        safetyForExpr(C->Cond.get(), FnMap, ValidExtents, PointerParams);
    Safe = combineSafety(std::move(Safe),
                         makeImplies(cloneVExpr(C->Cond.get()),
                                     safetyForExpr(C->Then.get(), FnMap,
                                                   ValidExtents, PointerParams),
                                     C->Loc),
                         C->Loc);
    return combineSafety(std::move(Safe),
                         makeImplies(makeNot(cloneVExpr(C->Cond.get()), C->Loc),
                                     safetyForExpr(C->Else.get(), FnMap,
                                                   ValidExtents, PointerParams),
                                     C->Loc),
                         C->Loc);
  }
  case VExpr::OverflowCheck: {
    const auto *O = static_cast<const VOverflowCheckExpr *>(E);
    auto Safe = safetyForExpr(O->Lhs.get(), FnMap, ValidExtents, PointerParams);
    if (O->Rhs)
      Safe = combineSafety(
          std::move(Safe),
          safetyForExpr(O->Rhs.get(), FnMap, ValidExtents, PointerParams),
          O->Loc);
    return Safe;
  }
  case VExpr::Forall:
  case VExpr::Exists: {
    const auto *Q = static_cast<const VQuantifiedExpr *>(E);
    auto Safe = combineSafety(
        safetyForExpr(Q->Lo.get(), FnMap, ValidExtents, PointerParams),
        safetyForExpr(Q->Hi.get(), FnMap, ValidExtents, PointerParams), Q->Loc);
    auto BodySafe =
        safetyForExpr(Q->Body.get(), FnMap, ValidExtents, PointerParams);
    auto Quantified = std::make_unique<VForallExpr>(
        Q->Binder, cloneVExpr(Q->Lo.get()), cloneVExpr(Q->Hi.get()),
        std::move(BodySafe), Q->Loc, Q->BinderType);
    return combineSafety(std::move(Safe), std::move(Quantified), Q->Loc);
  }
  case VExpr::HeapStore: {
    const auto *H = static_cast<const VHeapStoreExpr *>(E);
    auto Safe = combineSafety(
        safetyForExpr(H->Ptr.get(), FnMap, ValidExtents, PointerParams),
        safetyForExpr(H->Val.get(), FnMap, ValidExtents, PointerParams),
        H->Loc);
    return combineSafety(std::move(Safe), nonNullSafety(H->Ptr.get(), H->Loc),
                         H->Loc);
  }
  case VExpr::FieldAccess:
    return safetyForExpr(static_cast<const VFieldAccessExpr *>(E)->Base.get(),
                         FnMap, ValidExtents, PointerParams);
  case VExpr::SpecCall: {
    const auto *C = static_cast<const VSpecCallExpr *>(E);
    auto Safe = makeBoolLiteral(true, C->Loc);
    for (const auto &Arg : C->Args)
      Safe = combineSafety(
          std::move(Safe),
          safetyForExpr(Arg.get(), FnMap, ValidExtents, PointerParams), C->Loc);
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
        Safe = combineSafety(
            std::move(Safe),
            safetyForExpr(Expanded.get(), FnMap, ValidExtents, PointerParams),
            C->Loc);
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
  case VExpr::Load: {
    const auto *Load = static_cast<const VLoadExpr *>(E);
    return combineSafety(
        machineMathBridgeForExpr(Load->Ptr.get(), FnMap, false),
        machineMathBridgeForExpr(Load->AccessCondition.get(), FnMap, false),
        Load->Loc);
  }
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
    const std::map<std::string, std::unique_ptr<VExpr>> *OldMap = nullptr,
    const std::set<std::string> *NormalizedPointerChecks = nullptr) {
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
                    OldMap, NormalizedPointerChecks),
        substParams(B->Rhs.get(), Map, Ctx, EntryHeap, HeapOverride, BoundVars,
                    OldMap, NormalizedPointerChecks),
        B->Ty, B->Loc);
  }
  case VExpr::UnaryOp: {
    const auto *U = static_cast<const VUnaryOpExpr *>(E);
    auto Operand =
        substParams(U->Operand.get(), Map, Ctx, EntryHeap, HeapOverride,
                    BoundVars, OldMap, NormalizedPointerChecks);
    const auto *OperandVar =
        U->Operand->K == VExpr::Var
            ? static_cast<const VVarExpr *>(U->Operand.get())
            : nullptr;
    if ((U->Op == VUnaryOp::ValidPtr || U->Op == VUnaryOp::InitializedPtr) &&
        OperandVar && NormalizedPointerChecks &&
        NormalizedPointerChecks->count(OperandVar->Name) &&
        !hasPointerProvenance(Operand.get()))
      if (const VExpr *Base = pointerBase(Operand.get()))
        Operand = cloneVExpr(Base);
    return std::make_unique<VUnaryOpExpr>(
        U->Op, std::move(Operand), U->Ty, U->Loc,
        stateHeapName(Ctx, VAllocationHeapName, U->AllocationHeapVar),
        stateHeapName(Ctx, VLivenessHeapName, U->LivenessHeapVar),
        stateHeapName(Ctx, VInitializationHeapName, U->InitializationHeapVar));
  }
  case VExpr::Cast: {
    const auto *C = static_cast<const VCastExpr *>(E);
    return std::make_unique<VCastExpr>(
        substParams(C->Inner.get(), Map, Ctx, EntryHeap, HeapOverride,
                    BoundVars, OldMap, NormalizedPointerChecks),
        C->FromTy, C->Ty, C->Loc);
  }
  case VExpr::Load: {
    const auto *L = static_cast<const VLoadExpr *>(E);
    std::string Heap =
        HeapOverride.empty() ? Ctx.Renames.at(VHeapName) : HeapOverride;
    return std::make_unique<VLoadExpr>(
        substParams(L->Ptr.get(), Map, Ctx, EntryHeap, HeapOverride, BoundVars,
                    OldMap, NormalizedPointerChecks),
        L->Ty, L->Loc, std::move(Heap),
        substParams(L->AccessCondition.get(), Map, Ctx, EntryHeap, HeapOverride,
                    BoundVars, OldMap, NormalizedPointerChecks));
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
                       std::move(BoundVars), OldMap, NormalizedPointerChecks);
  }
  case VExpr::Conditional: {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    return std::make_unique<VConditionalExpr>(
        substParams(C->Cond.get(), Map, Ctx, EntryHeap, HeapOverride, BoundVars,
                    OldMap, NormalizedPointerChecks),
        substParams(C->Then.get(), Map, Ctx, EntryHeap, HeapOverride, BoundVars,
                    OldMap, NormalizedPointerChecks),
        substParams(C->Else.get(), Map, Ctx, EntryHeap, HeapOverride, BoundVars,
                    OldMap, NormalizedPointerChecks),
        C->Ty, C->Loc);
  }
  case VExpr::FieldAccess: {
    const auto *F = static_cast<const VFieldAccessExpr *>(E);
    return std::make_unique<VFieldAccessExpr>(
        substParams(F->Base.get(), Map, Ctx, EntryHeap, HeapOverride, BoundVars,
                    OldMap, NormalizedPointerChecks),
        F->Field, F->Ty, F->Loc);
  }
  case VExpr::SpecCall: {
    const auto *C = static_cast<const VSpecCallExpr *>(E);
    std::vector<std::unique_ptr<VExpr>> Args;
    for (const auto &Arg : C->Args)
      Args.push_back(substParams(Arg.get(), Map, Ctx, EntryHeap, HeapOverride,
                                 BoundVars, OldMap, NormalizedPointerChecks));
    return std::make_unique<VSpecCallExpr>(C->Callee, C->CalleeIdentity,
                                           std::move(Args), C->Ty, C->Loc);
  }
  case VExpr::OverflowCheck: {
    const auto *O = static_cast<const VOverflowCheckExpr *>(E);
    return std::make_unique<VOverflowCheckExpr>(
        O->Op,
        substParams(O->Lhs.get(), Map, Ctx, EntryHeap, HeapOverride, BoundVars,
                    OldMap, NormalizedPointerChecks),
        O->Rhs ? substParams(O->Rhs.get(), Map, Ctx, EntryHeap, HeapOverride,
                             BoundVars, OldMap, NormalizedPointerChecks)
               : nullptr,
        O->Loc);
  }
  case VExpr::Forall:
  case VExpr::Exists: {
    const auto *Q = static_cast<const VQuantifiedExpr *>(E);
    std::set<std::string> BodyBound = BoundVars;
    BodyBound.insert(Q->Binder);
    auto Lo = substParams(Q->Lo.get(), Map, Ctx, EntryHeap, HeapOverride,
                          BoundVars, OldMap, NormalizedPointerChecks);
    auto Hi = substParams(Q->Hi.get(), Map, Ctx, EntryHeap, HeapOverride,
                          BoundVars, OldMap, NormalizedPointerChecks);
    auto Body =
        substParams(Q->Body.get(), Map, Ctx, EntryHeap, HeapOverride,
                    std::move(BodyBound), OldMap, NormalizedPointerChecks);
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
                    OldMap, NormalizedPointerChecks),
        substParams(H->Val.get(), Map, Ctx, EntryHeap, HeapOverride, BoundVars,
                    OldMap, NormalizedPointerChecks),
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
  struct StoredPointerCell {
    std::unique_ptr<VExpr> Address;
    VType PointerType;
    std::unique_ptr<VExpr> Guard;
  };

  std::map<std::string, int> Versions;
  std::map<std::string, VType> Types;
  std::map<std::string, std::unique_ptr<VExpr>> OldState;
  std::vector<ReturnCase> ReturnCases;
  std::vector<FieldReturnCase> FieldReturnCases;
  std::vector<std::unique_ptr<VExpr>> ReturnGuards;
  std::vector<std::string> OwnedAllocationIdentities;
  std::map<std::string, std::unique_ptr<VExpr>> ReferenceBindings;
  std::set<std::string> PointerValueVariables;
  std::set<std::string> ProvenanceVariables;
  std::vector<VValidExtent> ActiveValidExtents;
  std::set<std::string> PointerParameterNames;
  std::set<std::string> SourcePointerParameterNames;
  std::set<std::string> RepresentedAllocationPointers;
  std::vector<StoredPointerCell> StoredPointerCells;
  std::set<std::string> HeapBases;
  std::set<std::string> HeapVariables;
  std::map<std::string, PassiveModelVariable> ModelVariables;
  std::map<std::string, std::set<std::string>> SourceVersions;
  std::set<std::string> SuppressedSourceVariables;
  std::vector<PassiveTraceEvent> TraceEvents;
  std::string ResultVar = "__result";
  const VFunction &Fn;
  FunctionMap FnMap;

  void recordSourceVersion(const std::string &Base,
                           const std::string &Versioned) {
    if (SuppressedSourceVariables.count(Base))
      return;
    auto Source = Fn.SourceVariables.find(Base);
    if (Source == Fn.SourceVariables.end())
      return;
    ModelVariables[Versioned] = {Source->second.DisplayName,
                                 Source->second.Type, Source->second.Loc,
                                 Source->second.EndLoc};
    SourceVersions[Base].insert(Versioned);
  }

  void suppressSourceVariable(const std::string &Base) {
    SuppressedSourceVariables.insert(Base);
    auto Versions = SourceVersions.find(Base);
    if (Versions == SourceVersions.end())
      return;
    for (const std::string &Versioned : Versions->second)
      ModelVariables.erase(Versioned);
    SourceVersions.erase(Versions);
  }

  std::string versionedName(const std::string &N) {
    int &V = Versions[N];
    std::string Name = N + "_" + std::to_string(V);
    if (HeapBases.count(N))
      HeapVariables.insert(Name);
    recordSourceVersion(N, Name);
    return Name;
  }

  std::string bump(const std::string &N) {
    std::string Name = N + "_" + std::to_string(++Versions[N]);
    if (HeapBases.count(N))
      HeapVariables.insert(Name);
    recordSourceVersion(N, Name);
    return Name;
  }

  std::unique_ptr<VExpr>
  resolveReferenceAddress(const VExpr *E,
                          std::set<std::string> Seen = {}) const {
    if (!E)
      return nullptr;
    const VExpr *Stripped = E;
    while (Stripped->K == VExpr::Cast)
      Stripped = static_cast<const VCastExpr *>(Stripped)->Inner.get();
    if (Stripped->K == VExpr::Var) {
      const std::string &Name = static_cast<const VVarExpr *>(Stripped)->Name;
      if (Seen.insert(Name).second)
        if (auto It = ReferenceBindings.find(Name);
            It != ReferenceBindings.end())
          return resolveReferenceAddress(It->second.get(), std::move(Seen));
    }
    return cloneVExpr(E);
  }

  void emitTrace(PassiveTraceKind Kind, std::string Message, const VExpr *Guard,
                 SourceLocation Loc,
                 std::vector<PassiveTraceValue> Values = {}) {
    PassiveTraceEvent Event;
    Event.Kind = Kind;
    Event.Message = std::move(Message);
    Event.Loc = Loc;
    Event.EndLoc = Loc;
    Event.Guard = Guard ? cloneVExpr(Guard) : makeBoolLiteral(true, Loc);
    for (PassiveTraceValue &Value : Values) {
      if (!Value.Value)
        continue;
      switch (Value.Value->Ty.Kind) {
      case VTypeKind::Bool:
      case VTypeKind::Int32:
      case VTypeKind::Int64:
      case VTypeKind::Ptr:
        Event.Values.push_back(std::move(Value));
        break;
      case VTypeKind::Void:
      case VTypeKind::Struct:
      case VTypeKind::Array:
      case VTypeKind::Unsupported:
        break;
      }
    }
    TraceEvents.push_back(std::move(Event));
  }

  void
  emitPassive(PassiveProgram &P, PassiveStmt::Kind K,
              std::unique_ptr<VExpr> Cond, const VExpr *Guard = nullptr,
              SourceLocation Loc = SourceLocation(),
              ProofObligationKind ProofKind = ProofObligationKind::Assertion) {
    auto PS = std::make_unique<PassiveStmt>();
    PS->K = K;
    PS->ProofKind = ProofKind;
    PS->TraceEventCount = TraceEvents.size();
    if (Guard)
      Cond = makeImplies(cloneVExpr(Guard), std::move(Cond), Loc);
    PS->Cond = std::move(Cond);
    P.Stmts.push_back(std::move(PS));
  }

  static bool needsInactiveFrame(const VExpr *Guard) {
    if (!Guard)
      return false;
    if (Guard->K != VExpr::Literal)
      return true;
    const auto &Literal = static_cast<const VLiteralExpr &>(*Guard);
    return Literal.Ty.Kind != VTypeKind::Bool || Literal.Value != "1";
  }

  void emitInactiveFrame(PassiveProgram &P, llvm::StringRef Before,
                         llvm::StringRef After, const VType &Ty,
                         const VExpr *Guard, SourceLocation Loc) {
    if (Before.empty() || After.empty() || Before == After ||
        !needsInactiveFrame(Guard))
      return;
    auto Inactive = makeNot(cloneVExpr(Guard), Loc);
    emitPassive(P, PassiveStmt::Assume,
                makeEq(std::make_unique<VVarExpr>(After.str(), Ty, Loc),
                       std::make_unique<VVarExpr>(Before.str(), Ty, Loc), Loc),
                Inactive.get(), Loc);
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
    case VStmt::EndLifetime:
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
      if (!C.ResultProvenanceTarget.empty())
        Out.insert(C.ResultProvenanceTarget);
      if (Callee != FnMap.end() && Callee->second->FreshOwnedReturn) {
        Out.insert(VHeapName);
        Out.insert(VAllocationHeapName);
        Out.insert(VAllocationBaseHeapName);
        Out.insert(VLivenessHeapName);
        Out.insert(VAllocationUsedHeapName);
        Out.insert(VInitializationHeapName);
        Out.insert(VAllocationSizeHeapName);
        Out.insert(VAllocationAlignHeapName);
      }
      if (Callee != FnMap.end() &&
          (!Callee->second->Modifies.empty() ||
           hasImplicitHeapEffect(*Callee->second, FnMap)))
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
                      bool BridgeMachineValue = false,
                      const VExpr *SafetySource = nullptr) {
    auto Safety = safetyForExpr(
        SafetySource ? SafetySource : E, &FnMap,
        SafetySource ? &Fn.ValidExtents : &ActiveValidExtents,
        SafetySource ? &SourcePointerParameterNames : &PointerParameterNames);
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
    emitInactiveFrame(P, Before, After, VType::makePtr(), Guard, Loc);
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

  void materializeFreshOwnedResult(
      PassiveProgram &P, std::map<std::string, std::string> &Renames,
      const VFreshOwnedReturn &Summary, const VType &PointerType,
      llvm::StringRef ResultTarget, llvm::StringRef PointerName,
      llvm::StringRef ProvenanceName, SourceLocation Loc) {
    auto Pointer = std::make_unique<VVarExpr>(PointerName.str(), PointerType,
                                              Loc, ProvenanceName.str());
    auto Provenance =
        std::make_unique<VVarExpr>(ProvenanceName.str(), VType::makePtr(), Loc);
    auto IsNull =
        makeEq(cloneVExpr(Pointer.get()),
               std::make_unique<VLiteralExpr>(0, VType::makePtr(), Loc), Loc);
    auto NonNull = makeNot(cloneVExpr(IsNull.get()), Loc);

    OwnedAllocationIdentities.push_back(ProvenanceName.str());
    RepresentedAllocationPointers.insert(ResultTarget.str());
    auto NonzeroProvenance = std::make_unique<VBinOpExpr>(
        VBinOp::Ne, cloneVExpr(Provenance.get()),
        std::make_unique<VLiteralExpr>(0, VType::makePtr(), Loc),
        VType::makeBool(), Loc);
    emitPassive(P, PassiveStmt::Assume, std::move(NonzeroProvenance));
    auto WasUsed = std::make_unique<VLoadExpr>(
        cloneVExpr(Provenance.get()), VType::makeBool(), Loc,
        Renames[VAllocationUsedHeapName]);
    emitPassive(P, PassiveStmt::Assume, makeNot(std::move(WasUsed), Loc));
    auto WasLive = std::make_unique<VLoadExpr>(cloneVExpr(Provenance.get()),
                                               VType::makeBool(), Loc,
                                               Renames[VLivenessHeapName]);
    emitPassive(P, PassiveStmt::Assume, makeNot(std::move(WasLive), Loc));
    updateHeap(P, Renames, VAllocationUsedHeapName,
               cloneVExpr(Provenance.get()), makeBoolLiteral(true, Loc),
               nullptr, Loc);
    if (!Summary.MayReturnNull)
      emitPassive(P, PassiveStmt::Assume, cloneVExpr(NonNull.get()));

    for (uint64_t Offset = 0; Offset < Summary.SizeBytes; ++Offset) {
      auto ByteNonNull = std::make_unique<VBinOpExpr>(
          VBinOp::Ne, addressOffset(Pointer.get(), Offset, Loc),
          std::make_unique<VLiteralExpr>(0, VType::makePtr(), Loc),
          VType::makeBool(), Loc);
      emitPassive(
          P, PassiveStmt::Assume,
          makeOr(cloneVExpr(IsNull.get()), std::move(ByteNonNull), Loc));
    }
    if (Summary.AlignBytes > 1) {
      auto Remainder = std::make_unique<VBinOpExpr>(
          VBinOp::Rem, cloneVExpr(Pointer.get()),
          std::make_unique<VLiteralExpr>(std::to_string(Summary.AlignBytes),
                                         VType::makePtr(), Loc),
          VType::makePtr(), Loc);
      auto Aligned =
          makeEq(std::move(Remainder),
                 std::make_unique<VLiteralExpr>(0, VType::makePtr(), Loc), Loc);
      emitPassive(P, PassiveStmt::Assume,
                  makeOr(cloneVExpr(IsNull.get()), std::move(Aligned), Loc));
    }

    CloneCtx Ctx{Renames, OldState, false};
    for (const std::string &Name : PointerValueVariables) {
      if (Name == ResultTarget || RepresentedAllocationPointers.count(Name))
        continue;
      auto TypeIt = Types.find(Name);
      auto RenameIt = Renames.find(Name);
      if (TypeIt == Types.end() || RenameIt == Renames.end() ||
          TypeIt->second.Kind != VTypeKind::Ptr ||
          TypeIt->second.PointeeSizeBytes == 0)
        continue;
      const VType &Ty = TypeIt->second;
      auto RawPointer = std::make_unique<VVarExpr>(Name, Ty, Loc);
      auto ExistingPointer = cloneExpr(RawPointer.get(), Ctx);
      auto IsLivePointer =
          cloneExpr(nonNullSafety(RawPointer.get(), Loc).get(), Ctx);
      auto NewBeforeExisting = std::make_unique<VBinOpExpr>(
          VBinOp::Le, addressOffset(Pointer.get(), Summary.SizeBytes, Loc),
          cloneVExpr(ExistingPointer.get()), VType::makeBool(), Loc);
      auto ExistingBeforeNew = std::make_unique<VBinOpExpr>(
          VBinOp::Le,
          addressOffset(ExistingPointer.get(), Ty.PointeeSizeBytes, Loc),
          cloneVExpr(Pointer.get()), VType::makeBool(), Loc);
      auto Disjoint = makeOr(std::move(NewBeforeExisting),
                             std::move(ExistingBeforeNew), Loc);
      auto Irrelevant = makeOr(cloneVExpr(IsNull.get()),
                               makeNot(std::move(IsLivePointer), Loc), Loc);
      emitPassive(P, PassiveStmt::Assume,
                  makeOr(std::move(Irrelevant), std::move(Disjoint), Loc));
    }

    for (const StoredPointerCell &Stored : StoredPointerCells) {
      if (!Stored.Address || Stored.PointerType.PointeeSizeBytes == 0)
        continue;
      auto CellLive =
          cloneExpr(exactPointerSafety(Stored.Address.get(), Loc).get(), Ctx);
      auto StoredValue = std::make_unique<VLoadExpr>(
          cloneVExpr(Stored.Address.get()), Stored.PointerType, Loc,
          Renames[VHeapName]);
      auto ValueLive =
          cloneExpr(exactPointerSafety(StoredValue.get(), Loc).get(), Ctx);
      auto NewBeforeStored = std::make_unique<VBinOpExpr>(
          VBinOp::Le, addressOffset(Pointer.get(), Summary.SizeBytes, Loc),
          cloneVExpr(StoredValue.get()), VType::makeBool(), Loc);
      auto StoredBeforeNew = std::make_unique<VBinOpExpr>(
          VBinOp::Le,
          addressOffset(StoredValue.get(), Stored.PointerType.PointeeSizeBytes,
                        Loc),
          cloneVExpr(Pointer.get()), VType::makeBool(), Loc);
      auto Disjoint =
          makeOr(std::move(NewBeforeStored), std::move(StoredBeforeNew), Loc);
      auto Irrelevant =
          makeOr(cloneVExpr(IsNull.get()),
                 makeNot(cloneVExpr(Stored.Guard.get()), Loc), Loc);
      Irrelevant =
          makeOr(std::move(Irrelevant), makeNot(std::move(CellLive), Loc), Loc);
      Irrelevant = makeOr(std::move(Irrelevant),
                          makeNot(std::move(ValueLive), Loc), Loc);
      emitPassive(P, PassiveStmt::Assume,
                  makeOr(std::move(Irrelevant), std::move(Disjoint), Loc));
    }

    CloneCtx EntryCtx{Renames, OldState, true};
    for (const VValidExtent &Extent : Fn.ValidExtents) {
      if (!Extent.Length || Extent.PointerType.PointeeSizeBytes == 0)
        continue;
      auto Base = cloneExpr(
          std::make_unique<VVarExpr>(Extent.Base, Extent.PointerType, Loc)
              .get(),
          EntryCtx);
      auto Length = cloneExpr(Extent.Length.get(), EntryCtx);
      auto Empty =
          makeEq(cloneVExpr(Length.get()),
                 std::make_unique<VLiteralExpr>(0, Length->Ty, Loc), Loc);
      VType MathType = Length->Ty;
      MathType.IntMode = VIntMode::Math;
      std::unique_ptr<VExpr> ByteLength;
      if (Length->Ty.IntMode == VIntMode::Math)
        ByteLength = cloneVExpr(Length.get());
      else
        ByteLength = std::make_unique<VCastExpr>(cloneVExpr(Length.get()),
                                                 Length->Ty, MathType, Loc);
      if (Extent.PointerType.PointeeSizeBytes > 1)
        ByteLength = std::make_unique<VBinOpExpr>(
            VBinOp::Mul, std::move(ByteLength),
            std::make_unique<VLiteralExpr>(
                std::to_string(Extent.PointerType.PointeeSizeBytes), MathType,
                Loc),
            MathType, Loc);
      auto SliceEnd = std::make_unique<VBinOpExpr>(
          VBinOp::Add, cloneVExpr(Base.get()), std::move(ByteLength),
          VType::makePtr(), Loc);
      auto NewBeforeSlice = std::make_unique<VBinOpExpr>(
          VBinOp::Le, addressOffset(Pointer.get(), Summary.SizeBytes, Loc),
          cloneVExpr(Base.get()), VType::makeBool(), Loc);
      auto SliceBeforeNew = std::make_unique<VBinOpExpr>(
          VBinOp::Le, std::move(SliceEnd), cloneVExpr(Pointer.get()),
          VType::makeBool(), Loc);
      auto Disjoint =
          makeOr(std::move(NewBeforeSlice), std::move(SliceBeforeNew), Loc);
      auto Irrelevant = makeOr(cloneVExpr(IsNull.get()), std::move(Empty), Loc);
      emitPassive(P, PassiveStmt::Assume,
                  makeOr(std::move(Irrelevant), std::move(Disjoint), Loc));
    }

    for (uint64_t Offset = 0; Offset < Summary.SizeBytes; ++Offset) {
      auto Address = addressOffset(Pointer.get(), Offset, Loc);
      auto Owner = std::make_unique<VLoadExpr>(cloneVExpr(Address.get()),
                                               VType::makePtr(), Loc,
                                               Renames[VAllocationHeapName]);
      auto Live = std::make_unique<VLoadExpr>(cloneVExpr(Owner.get()),
                                              VType::makeBool(), Loc,
                                              Renames[VLivenessHeapName]);
      emitPassive(
          P, PassiveStmt::Assume,
          makeOr(cloneVExpr(IsNull.get()), makeNot(std::move(Live), Loc), Loc));
      auto OwnerAfter = std::make_unique<VConditionalExpr>(
          cloneVExpr(IsNull.get()), std::move(Owner),
          cloneVExpr(Provenance.get()), VType::makePtr(), Loc);
      updateHeap(P, Renames, VAllocationHeapName, std::move(Address),
                 std::move(OwnerAfter), nullptr, Loc);
    }
    updateHeap(P, Renames, VAllocationBaseHeapName,
               cloneVExpr(Provenance.get()), cloneVExpr(Pointer.get()), nullptr,
               Loc);
    updateHeap(P, Renames, VAllocationSizeHeapName,
               cloneVExpr(Provenance.get()),
               std::make_unique<VLiteralExpr>(std::to_string(Summary.SizeBytes),
                                              VType::makePtr(), Loc),
               nullptr, Loc);
    updateHeap(P, Renames, VAllocationAlignHeapName,
               cloneVExpr(Provenance.get()),
               std::make_unique<VLiteralExpr>(
                   std::to_string(Summary.AlignBytes), VType::makePtr(), Loc),
               nullptr, Loc);
    updateHeap(P, Renames, VLivenessHeapName, cloneVExpr(Provenance.get()),
               std::move(NonNull), nullptr, Loc);

    const std::string HeapBefore = Renames[VHeapName];
    const std::string HeapAfter = bump(VHeapName);
    Renames[VHeapName] = HeapAfter;
    const std::string FreshValueName = bump("__owned_call_value");
    auto ExistingValue = std::make_unique<VLoadExpr>(
        cloneVExpr(Pointer.get()), Summary.AllocatedType, Loc, HeapBefore);
    auto StoredValue = std::make_unique<VConditionalExpr>(
        cloneVExpr(IsNull.get()), std::move(ExistingValue),
        std::make_unique<VVarExpr>(FreshValueName, Summary.AllocatedType, Loc),
        Summary.AllocatedType, Loc);
    emitPassive(P, PassiveStmt::Assume,
                std::make_unique<VHeapStoreExpr>(HeapBefore, HeapAfter,
                                                 cloneVExpr(Pointer.get()),
                                                 std::move(StoredValue), Loc));

    auto WasInitialized = std::make_unique<VLoadExpr>(
        cloneVExpr(Pointer.get()), VType::makeBool(), Loc,
        Renames[VInitializationHeapName]);
    auto InitializedAfter = std::make_unique<VConditionalExpr>(
        cloneVExpr(IsNull.get()), std::move(WasInitialized),
        makeBoolLiteral(true, Loc), VType::makeBool(), Loc);
    updateHeap(P, Renames, VInitializationHeapName, cloneVExpr(Pointer.get()),
               std::move(InitializedAfter), nullptr, Loc);
  }

public:
  PassivizerImpl(const VFunction &Fn, FunctionMap FnMap)
      : Fn(Fn), FnMap(std::move(FnMap)) {}

  PassiveProgram run() {
    PassiveProgram P;
    P.FunctionName = Fn.Name;
    P.FunctionIdentity = Fn.Identity;
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
      HeapBases.insert(Heap);
      Versions[Heap] = 0;
      Types[Heap] = VType::makePtr();
    }
    Types["result"] = Fn.ReturnType;
    for (const auto &Param : Fn.Params) {
      Types[Param.first] = Param.second;
      if (Param.second.Kind == VTypeKind::Ptr)
        PointerValueVariables.insert(Param.first);
    }
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
      if (Param.second.Kind == VTypeKind::Ptr) {
        PointerParameterNames.insert(V0);
        SourcePointerParameterNames.insert(Param.first);
      }
    }
    CloneCtx EntryCtx{Renames, OldState, true};
    for (const VValidExtent &Extent : Fn.ValidExtents)
      ActiveValidExtents.emplace_back(stateVariableName(EntryCtx, Extent.Base),
                                      Extent.PointerType,
                                      cloneExpr(Extent.Length.get(), EntryCtx));

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
      auto Safety = safetyForExpr(Post.get(), &FnMap, &Fn.ValidExtents,
                                  &SourcePointerParameterNames);
      P.ExitAsserts.push_back(cloneExpr(Safety.get(), PCtx));
      P.ExitAsserts.push_back(std::move(BoundPost));
    }
    P.OldHeapName = Heap0;
    P.HeapVariables = HeapVariables;
    P.ModelVariables = std::move(ModelVariables);
    P.TraceEvents = std::move(TraceEvents);
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
    const bool ReturnsFreshOwned =
        Callee->FreshOwnedReturn && Callee->ReturnType.Kind == VTypeKind::Ptr &&
        !C.ResultTarget.empty() && !C.ResultProvenanceTarget.empty();
    if (Callee->UsesDynamicStorage && !ReturnsFreshOwned) {
      emitPassive(P, PassiveStmt::Assert, makeBoolLiteral(false, C.Loc));
      return;
    }
    const std::string EntryHeap = Renames[VHeapName];
    CloneCtx Ctx{Renames, OldState, false};
    std::map<std::string, std::unique_ptr<VExpr>> ParamMap;
    for (unsigned I = 0; I < Callee->Params.size() && I < C.Args.size(); ++I)
      ParamMap[Callee->Params[I].first] = cloneExpr(C.Args[I].get(), Ctx);
    std::set<std::string> DynamicParams;
    std::set<std::pair<std::string, std::string>> ActiveScans;
    for (const auto &Param : Callee->Params)
      if (auto It = ParamMap.find(Param.first);
          It != ParamMap.end() && hasPointerProvenance(It->second.get())) {
        DynamicParams.insert(Param.first);
        if (Callee->IsProof || Callee->IsExternalContract ||
            !scalarDynamicCalleeSafe(*Callee, Param.first, FnMap,
                                     ActiveScans)) {
          emitPassive(P, PassiveStmt::Assert, makeBoolLiteral(false, C.Loc));
          return;
        }
      }
    if (!C.ResultProvenanceTarget.empty() && DynamicParams.empty() &&
        !ReturnsFreshOwned) {
      emitPassive(P, PassiveStmt::Assert, makeBoolLiteral(false, C.Loc));
      return;
    }
    if (Callee->ReturnType.Kind == VTypeKind::Ptr && !C.ResultTarget.empty() &&
        !ReturnsFreshOwned && !DynamicParams.empty() &&
        (C.ResultProvenanceTarget.empty() ||
         !pointerReturnsComeFrom(*Callee, DynamicParams))) {
      emitPassive(P, PassiveStmt::Assert, makeBoolLiteral(false, C.Loc));
      return;
    }
    for (unsigned I = 0; I < Callee->Params.size() && I < C.Args.size(); ++I)
      emitExprSafety(P, ParamMap[Callee->Params[I].first].get(), nullptr, C.Loc,
                     Renames, true, C.Args[I].get());
    const bool HasImplicitHeapEffect =
        !ReturnsFreshOwned && hasImplicitHeapEffect(*Callee, FnMap);
    for (const VValidExtent &Extent : Callee->ValidExtents) {
      auto Actual = ParamMap.find(Extent.Base);
      if (Actual == ParamMap.end()) {
        emitPassive(P, PassiveStmt::Assert, makeBoolLiteral(false, C.Loc));
        continue;
      }
      auto Length = substParams(Extent.Length.get(), ParamMap, Ctx, EntryHeap);
      auto Contained = sliceContainment(Actual->second.get(), Length.get(),
                                        Extent.PointerType.PointeeSizeBytes,
                                        ActiveValidExtents, C.Loc);
      if (HasImplicitHeapEffect ||
          hasUnboundedExtentWrite(*Callee, Extent.Base))
        Contained =
            makeAnd(std::move(Contained), makeBoolLiteral(false, C.Loc), C.Loc);
      emitPassive(P, PassiveStmt::Assert, std::move(Contained), nullptr, C.Loc);
      auto LengthValue = asPointerOffset(Length.get());
      if (!LengthValue) {
        emitPassive(P, PassiveStmt::Assert, makeBoolLiteral(false, C.Loc));
        continue;
      }
      auto Empty = std::make_unique<VBinOpExpr>(
          VBinOp::Eq, std::move(LengthValue),
          std::make_unique<VLiteralExpr>(0, pointerOffsetType(), C.Loc),
          VType::makeBool(), C.Loc);
      auto NonNull = std::make_unique<VBinOpExpr>(
          VBinOp::Ne, cloneVExpr(Actual->second.get()),
          std::make_unique<VLiteralExpr>(0, VType::makePtr(), C.Loc),
          VType::makeBool(), C.Loc);
      emitPassive(P, PassiveStmt::Assume,
                  makeOr(std::move(Empty), std::move(NonNull), C.Loc), nullptr,
                  C.Loc);
    }

    std::vector<std::unique_ptr<VExpr>> ActualModifies;
    for (const auto &M : Callee->Modifies)
      ActualModifies.push_back(
          substParams(M.get(), ParamMap, Ctx, EntryHeap, EntryHeap));
    std::vector<std::unique_ptr<VExpr>> CallerModifies;
    CloneCtx CallerEntryCtx{Renames, OldState, true};
    for (const auto &M : Fn.Modifies)
      CallerModifies.push_back(cloneExpr(M.get(), CallerEntryCtx));

    std::set<std::string> CalleePointerParams;
    for (const auto &[Name, Ty] : Callee->Params)
      if (Ty.Kind == VTypeKind::Ptr)
        CalleePointerParams.insert(Name);
    std::set<std::string> ContainedPointerParams;
    for (const VValidExtent &Extent : Callee->ValidExtents)
      ContainedPointerParams.insert(Extent.Base);
    for (const auto &Pre : Callee->Preconditions) {
      auto BoundPre = substParams(Pre.get(), ParamMap, Ctx, EntryHeap, "", {},
                                  nullptr, &ContainedPointerParams);
      auto PreSafety = safetyForExpr(Pre.get(), &FnMap, &Callee->ValidExtents,
                                     &CalleePointerParams);
      emitPassive(P, PassiveStmt::Assert,
                  substParams(PreSafety.get(), ParamMap, Ctx, EntryHeap),
                  nullptr, C.Loc);
      emitMathBridge(P, BoundPre.get(), nullptr, C.Loc);
      emitPassive(P, PassiveStmt::Assert, std::move(BoundPre), nullptr, C.Loc);
    }

    for (size_t I = 0; I < ActualModifies.size(); ++I) {
      const auto &M = ActualModifies[I];
      emitExprSafety(P, M.get(), nullptr, M->Loc, Renames);
      auto Allowed = makeBoolLiteral(false, C.Loc);
      const auto *ActualLoad = M && M->K == VExpr::Load
                                   ? static_cast<const VLoadExpr *>(M.get())
                                   : nullptr;
      if (ActualLoad) {
        const bool ActualIsRegion = I >= Callee->Modifies.size() ||
                                    isRegionFootprint(Callee->Modifies[I].get(),
                                                      Callee->ReferenceParams);
        if (auto Provenance = pointerProvenance(ActualLoad->Ptr.get()))
          for (const std::string &Identity : OwnedAllocationIdentities)
            Allowed = makeOr(std::move(Allowed),
                             makeEq(cloneVExpr(Provenance.get()),
                                    std::make_unique<VVarExpr>(
                                        Identity, VType::makePtr(), C.Loc),
                                    C.Loc),
                             C.Loc);
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
                                      isRegionFootprint(Fn.Modifies[J].get(),
                                                        Fn.ReferenceParams),
                                  ActualLoad->Ptr.get(), ActualIsRegion, C.Loc),
                C.Loc);
        }
      }
      emitPassive(P, PassiveStmt::Assert, std::move(Allowed), nullptr, C.Loc);
    }

    if (HasImplicitHeapEffect) {
      bool CallerHasPointerParam = false;
      for (const auto &Param : Fn.Params)
        CallerHasPointerParam |= Param.second.Kind == VTypeKind::Ptr;
      bool AllPointerParamsOwned = true;
      for (const auto &Param : Callee->Params)
        if (Param.second.Kind == VTypeKind::Ptr)
          AllPointerParamsOwned &= DynamicParams.count(Param.first);
      const bool CallerAllowsImplicitHeapEffect =
          !Fn.IsProof && Fn.Modifies.empty() &&
          (CallerHasPointerParam || AllPointerParamsOwned);
      emitPassive(P, PassiveStmt::Assert,
                  makeBoolLiteral(CallerAllowsImplicitHeapEffect, C.Loc),
                  nullptr, C.Loc);
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
        std::string ProvenanceVer;
        if (Callee->ReturnType.Kind == VTypeKind::Ptr &&
            !C.ResultProvenanceTarget.empty()) {
          ProvenanceVer = bump(C.ResultProvenanceTarget);
          Renames[C.ResultProvenanceTarget] = ProvenanceVer;
          Types[C.ResultProvenanceTarget] = VType::makePtr();
          ProvenanceVariables.insert(C.ResultProvenanceTarget);
          PointerValueVariables.erase(C.ResultProvenanceTarget);
        }
        if (Callee->ReturnType.Kind == VTypeKind::Ptr &&
            !C.ResultTarget.empty())
          PointerValueVariables.insert(C.ResultTarget);
        ParamMap["result"] = std::make_unique<VVarExpr>(
            RetVer, Callee->ReturnType, C.Loc, std::move(ProvenanceVer));
        if (ReturnsFreshOwned)
          materializeFreshOwnedResult(
              P, Renames, *Callee->FreshOwnedReturn, Callee->ReturnType,
              C.ResultTarget, RetVer, Renames[C.ResultProvenanceTarget], C.Loc);
      }
    }

    bool CanFrameExactly = !ActualModifies.empty();
    for (size_t I = 0; I < ActualModifies.size(); ++I)
      if (!ActualModifies[I] || ActualModifies[I]->K != VExpr::Load ||
          I >= Callee->Modifies.size() ||
          (isRegionFootprint(Callee->Modifies[I].get(),
                             Callee->ReferenceParams) &&
           !hasPointerProvenance(
               static_cast<const VLoadExpr *>(ActualModifies[I].get())
                   ->Ptr.get())))
        CanFrameExactly = false;
    if ((!ActualModifies.empty() && !CanFrameExactly) ||
        HasImplicitHeapEffect) {
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
      if (A.Value && A.Value->Ty.Kind == VTypeKind::Ptr) {
        const auto *V = A.Value->K == VExpr::Var
                            ? static_cast<const VVarExpr *>(A.Value.get())
                            : nullptr;
        if (V && !V->ProvenanceVariable.empty()) {
          ProvenanceVariables.insert(V->ProvenanceVariable);
          PointerValueVariables.erase(V->ProvenanceVariable);
        }
        if (V && V->ProvenanceVariable.empty() &&
            ProvenanceVariables.count(V->Name)) {
          ProvenanceVariables.insert(A.Target);
          PointerValueVariables.erase(A.Target);
        } else if (!ProvenanceVariables.count(A.Target)) {
          PointerValueVariables.insert(A.Target);
        }
      }
      CloneCtx Ctx{Renames, OldState, false};
      auto Val = cloneExpr(A.Value.get(), Ctx);
      emitExprSafety(P, Val.get(), Active.get(), A.Loc, Renames, true,
                     A.Value.get());
      Types[A.Target] = Val->Ty;
      const std::string PreviousName = Renames[A.Target];
      std::string NewName = bump(A.Target);
      Renames[A.Target] = NewName;
      VType ValueTy = Val->Ty;
      if (A.IsReferenceBinding)
        ReferenceBindings[NewName] = cloneVExpr(Val.get());
      emitPassive(P, PassiveStmt::Assume,
                  makeEq(std::make_unique<VVarExpr>(NewName, ValueTy, A.Loc),
                         std::move(Val), A.Loc),
                  Active.get(), A.Loc);
      emitInactiveFrame(P, PreviousName, NewName, ValueTy, Active.get(), A.Loc);
      break;
    }
    case VStmt::Store: {
      const auto &St = static_cast<const VStoreStmt &>(S);
      CloneCtx Ctx{Renames, OldState, false};
      auto Ptr = cloneExpr(St.Ptr.get(), Ctx);
      auto Val = cloneExpr(St.Value.get(), Ctx);
      auto AccessCondition = cloneExpr(St.AccessCondition.get(), Ctx);
      std::vector<PassiveTraceValue> TraceValues;
      TraceValues.push_back({"address", cloneVExpr(Ptr.get())});
      TraceValues.push_back({"value", cloneVExpr(Val.get())});
      emitTrace(PassiveTraceKind::HeapWrite, "store", Active.get(), St.Loc,
                std::move(TraceValues));
      emitExprSafety(P, Ptr.get(), Active.get(), St.Loc, Renames, false,
                     St.Ptr.get());
      emitExprSafety(P, Val.get(), Active.get(), St.Loc, Renames, true,
                     St.Value.get());
      if (Val->Ty.Kind == VTypeKind::Ptr && hasPointerProvenance(Val.get())) {
        emitPassive(P, PassiveStmt::Assert, makeBoolLiteral(false, St.Loc),
                    Active.get(), St.Loc);
        break;
      }
      std::unique_ptr<VExpr> PointerCell =
          Val->Ty.Kind == VTypeKind::Ptr ? cloneVExpr(Ptr.get()) : nullptr;
      const VType StoredPointerType = Val->Ty;
      if (AccessCondition) {
        emitExprSafety(P, AccessCondition.get(), Active.get(), St.Loc, Renames,
                       false, St.AccessCondition.get());
        emitPassive(P, PassiveStmt::Assert, std::move(AccessCondition),
                    Active.get(), St.Loc);
      }
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
          auto EffectivePtr = resolveReferenceAddress(Ptr.get());
          Allowed = makeOr(
              std::move(Allowed),
              footprintContains(DeclaredPtr.get(),
                                isRegionFootprint(M.get(), Fn.ReferenceParams),
                                EffectivePtr.get(), false, St.Loc),
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
      emitInactiveFrame(P, OldHeap, NewHeap, VType::makePtr(), Active.get(),
                        St.Loc);
      if (PointerCell)
        StoredPointerCells.push_back({std::move(PointerCell), StoredPointerType,
                                      cloneVExpr(Active.get())});
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
        emitExprSafety(P, Initializer.get(), Active.get(), A.Loc, Renames, true,
                       A.Initializer.get());
      }

      if (A.IsAutomatic)
        suppressSourceVariable(A.Target);
      Types[A.Target] = VType::makePtr(A.SizeBytes);
      Types[A.ProvenanceTarget] = VType::makePtr();
      const std::string PointerName = bump(A.Target);
      const std::string ProvenanceName = bump(A.ProvenanceTarget);
      Renames[A.Target] = PointerName;
      Renames[A.ProvenanceTarget] = ProvenanceName;
      OwnedAllocationIdentities.push_back(ProvenanceName);
      ProvenanceVariables.insert(A.ProvenanceTarget);
      PointerValueVariables.erase(A.ProvenanceTarget);
      auto Pointer = std::make_unique<VVarExpr>(
          PointerName, VType::makePtr(A.SizeBytes), A.Loc, ProvenanceName);
      auto Provenance =
          std::make_unique<VVarExpr>(ProvenanceName, VType::makePtr(), A.Loc);
      std::vector<PassiveTraceValue> TraceValues;
      TraceValues.push_back({"address", cloneVExpr(Pointer.get())});
      TraceValues.push_back({"provenance", cloneVExpr(Provenance.get())});
      emitTrace(PassiveTraceKind::Allocation,
                A.IsAutomatic ? "automatic allocation" : "allocation",
                Active.get(), A.Loc, std::move(TraceValues));

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
      auto WasLive = std::make_unique<VLoadExpr>(cloneVExpr(Provenance.get()),
                                                 VType::makeBool(), A.Loc,
                                                 Renames[VLivenessHeapName]);
      emitPassive(P, PassiveStmt::Assume, makeNot(std::move(WasLive), A.Loc),
                  Active.get(), A.Loc);
      updateHeap(P, Renames, VAllocationUsedHeapName,
                 cloneVExpr(Provenance.get()), makeBoolLiteral(true, A.Loc),
                 Active.get(), A.Loc);

      // No byte of a real object lives at the null address, so interior
      // subobject addresses are usable as references, not just the base.
      for (uint64_t Offset = 0; Offset < A.SizeBytes; ++Offset) {
        auto NonNull = std::make_unique<VBinOpExpr>(
            VBinOp::Ne, addressOffset(Pointer.get(), Offset, A.Loc),
            std::make_unique<VLiteralExpr>(0, VType::makePtr(), A.Loc),
            VType::makeBool(), A.Loc);
        emitPassive(P, PassiveStmt::Assume, std::move(NonNull), Active.get(),
                    A.Loc);
      }
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
      // Fresh storage cannot overlap any currently live pointer value,
      // including a result returned by an earlier modular call. Represented
      // allocations need no pairwise condition: their per-byte live ownership
      // below already prevents overlap.
      for (const std::string &Name : PointerValueVariables) {
        if (Name == A.Target || RepresentedAllocationPointers.count(Name))
          continue;
        auto TypeIt = Types.find(Name);
        auto RenameIt = Renames.find(Name);
        if (TypeIt == Types.end() || RenameIt == Renames.end() ||
            TypeIt->second.Kind != VTypeKind::Ptr)
          continue;
        const VType &Ty = TypeIt->second;
        auto RawPointer = std::make_unique<VVarExpr>(Name, Ty, A.Loc);
        auto ExistingPointer = cloneExpr(RawPointer.get(), Ctx);
        auto IsLivePointer =
            cloneExpr(nonNullSafety(RawPointer.get(), A.Loc).get(), Ctx);
        if (Ty.PointeeSizeBytes == 0)
          continue;
        auto LocalBeforeExisting = std::make_unique<VBinOpExpr>(
            VBinOp::Le, addressOffset(Pointer.get(), A.SizeBytes, A.Loc),
            cloneVExpr(ExistingPointer.get()), VType::makeBool(), A.Loc);
        auto ExistingBeforeLocal = std::make_unique<VBinOpExpr>(
            VBinOp::Le,
            addressOffset(ExistingPointer.get(), Ty.PointeeSizeBytes, A.Loc),
            cloneVExpr(Pointer.get()), VType::makeBool(), A.Loc);
        auto Disjoint = makeOr(std::move(LocalBeforeExisting),
                               std::move(ExistingBeforeLocal), A.Loc);
        emitPassive(P, PassiveStmt::Assume,
                    makeOr(makeNot(std::move(IsLivePointer), A.Loc),
                           std::move(Disjoint), A.Loc),
                    Active.get(), A.Loc);
      }

      // Pointer leaves in promoted objects retain their numeric value but not a
      // provenance companion. Load the current cell value so overwrites do not
      // retain stale constraints, and require validity at the exact loaded
      // address so a one-past value does not acquire a fictitious pointee.
      for (const StoredPointerCell &Stored : StoredPointerCells) {
        if (!Stored.Address || Stored.PointerType.PointeeSizeBytes == 0)
          continue;
        auto CellLive = cloneExpr(
            exactPointerSafety(Stored.Address.get(), A.Loc).get(), Ctx);
        auto StoredValue = std::make_unique<VLoadExpr>(
            cloneVExpr(Stored.Address.get()), Stored.PointerType, A.Loc,
            Renames[VHeapName]);
        auto ValueLive =
            cloneExpr(exactPointerSafety(StoredValue.get(), A.Loc).get(), Ctx);
        auto LocalBeforeStored = std::make_unique<VBinOpExpr>(
            VBinOp::Le, addressOffset(Pointer.get(), A.SizeBytes, A.Loc),
            cloneVExpr(StoredValue.get()), VType::makeBool(), A.Loc);
        auto StoredBeforeLocal = std::make_unique<VBinOpExpr>(
            VBinOp::Le,
            addressOffset(StoredValue.get(),
                          Stored.PointerType.PointeeSizeBytes, A.Loc),
            cloneVExpr(Pointer.get()), VType::makeBool(), A.Loc);
        auto Disjoint = makeOr(std::move(LocalBeforeStored),
                               std::move(StoredBeforeLocal), A.Loc);
        auto Irrelevant = makeOr(makeNot(cloneVExpr(Stored.Guard.get()), A.Loc),
                                 makeNot(std::move(CellLive), A.Loc), A.Loc);
        Irrelevant = makeOr(std::move(Irrelevant),
                            makeNot(std::move(ValueLive), A.Loc), A.Loc);
        emitPassive(P, PassiveStmt::Assume,
                    makeOr(std::move(Irrelevant), std::move(Disjoint), A.Loc),
                    Active.get(), A.Loc);
      }

      // A valid(base, count) contract denotes the complete incoming slice, not
      // merely its first pointee. Preserve that half-open range when choosing
      // numeric addresses for fresh storage.
      CloneCtx EntryCtx{Renames, OldState, true};
      for (const VValidExtent &Extent : Fn.ValidExtents) {
        if (!Extent.Length || Extent.PointerType.PointeeSizeBytes == 0)
          continue;
        auto Base = cloneExpr(
            std::make_unique<VVarExpr>(Extent.Base, Extent.PointerType, A.Loc)
                .get(),
            EntryCtx);
        auto Length = cloneExpr(Extent.Length.get(), EntryCtx);
        auto Empty =
            makeEq(cloneVExpr(Length.get()),
                   std::make_unique<VLiteralExpr>(0, Length->Ty, A.Loc), A.Loc);
        VType MathType = Length->Ty;
        MathType.IntMode = VIntMode::Math;
        std::unique_ptr<VExpr> ByteLength;
        if (Length->Ty.IntMode == VIntMode::Math)
          ByteLength = cloneVExpr(Length.get());
        else
          ByteLength = std::make_unique<VCastExpr>(cloneVExpr(Length.get()),
                                                   Length->Ty, MathType, A.Loc);
        if (Extent.PointerType.PointeeSizeBytes > 1)
          ByteLength = std::make_unique<VBinOpExpr>(
              VBinOp::Mul, std::move(ByteLength),
              std::make_unique<VLiteralExpr>(
                  std::to_string(Extent.PointerType.PointeeSizeBytes), MathType,
                  A.Loc),
              MathType, A.Loc);
        auto SliceEnd = std::make_unique<VBinOpExpr>(
            VBinOp::Add, cloneVExpr(Base.get()), std::move(ByteLength),
            VType::makePtr(), A.Loc);
        auto LocalBeforeSlice = std::make_unique<VBinOpExpr>(
            VBinOp::Le, addressOffset(Pointer.get(), A.SizeBytes, A.Loc),
            cloneVExpr(Base.get()), VType::makeBool(), A.Loc);
        auto SliceBeforeLocal = std::make_unique<VBinOpExpr>(
            VBinOp::Le, std::move(SliceEnd), cloneVExpr(Pointer.get()),
            VType::makeBool(), A.Loc);
        auto Disjoint = makeOr(std::move(LocalBeforeSlice),
                               std::move(SliceBeforeLocal), A.Loc);
        emitPassive(P, PassiveStmt::Assume,
                    makeOr(std::move(Empty), std::move(Disjoint), A.Loc),
                    Active.get(), A.Loc);
      }
      PointerValueVariables.insert(A.Target);
      RepresentedAllocationPointers.insert(A.Target);

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
      if (Initializer) {
        updateHeap(P, Renames, VInitializationHeapName,
                   cloneVExpr(Pointer.get()), makeBoolLiteral(true, A.Loc),
                   Active.get(), A.Loc);
        updateHeap(P, Renames, VHeapName, cloneVExpr(Pointer.get()),
                   std::move(Initializer), Active.get(), A.Loc);
      } else {
        // Fresh storage is uninitialized at every target byte, so a promoted
        // aggregate only becomes readable at the leaves its declaration stores
        // to. Stale initialization bits from earlier allocations at the same
        // address cannot leak in.
        for (uint64_t Offset = 0; Offset < A.SizeBytes; ++Offset)
          updateHeap(P, Renames, VInitializationHeapName,
                     addressOffset(Pointer.get(), Offset, A.Loc),
                     makeBoolLiteral(false, A.Loc), Active.get(), A.Loc);
      }
      break;
    }
    case VStmt::EndLifetime: {
      const auto &E = static_cast<const VEndLifetimeStmt &>(S);
      // The frontend has already proved that automatic addresses cannot
      // escape. A function-exit transition is therefore unobservable and may
      // be erased from the obligation, while lexical inner-scope transitions
      // must update liveness for following code.
      if (E.IsFunctionExit)
        break;
      CloneCtx Ctx{Renames, OldState, false};
      auto Provenance =
          cloneExpr(std::make_unique<VVarExpr>(E.ProvenanceTarget,
                                               VType::makePtr(), E.Loc)
                        .get(),
                    Ctx);
      std::vector<PassiveTraceValue> TraceValues;
      TraceValues.push_back({"provenance", cloneVExpr(Provenance.get())});
      emitTrace(PassiveTraceKind::LifetimeEnd, "lifetime end", Active.get(),
                E.Loc, std::move(TraceValues));
      updateHeap(P, Renames, VLivenessHeapName, std::move(Provenance),
                 makeBoolLiteral(false, E.Loc), Active.get(), E.Loc);
      break;
    }
    case VStmt::Free: {
      const auto &F = static_cast<const VFreeStmt &>(S);
      CloneCtx Ctx{Renames, OldState, false};
      auto Pointer = cloneExpr(F.Ptr.get(), Ctx);
      std::vector<PassiveTraceValue> TraceValues;
      TraceValues.push_back({"address", cloneVExpr(Pointer.get())});
      emitTrace(PassiveTraceKind::Deallocation, "delete", Active.get(), F.Loc,
                std::move(TraceValues));
      emitExprSafety(P, Pointer.get(), Active.get(), F.Loc, Renames, false,
                     F.Ptr.get());
      auto Provenance = pointerProvenance(Pointer.get());
      if (!Provenance) {
        emitPassive(
            P, PassiveStmt::Assert,
            makeEq(std::move(Pointer),
                   std::make_unique<VLiteralExpr>(0, VType::makePtr(), F.Loc),
                   F.Loc),
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
      emitExprSafety(P, Cond.get(), Active.get(), I.Loc, Renames, false,
                     I.Cond.get());
      auto EntryActive = cloneVExpr(Active.get());
      const auto EntryRenames = Renames;
      auto ThenRenames = Renames;
      auto ElseRenames = Renames;
      auto ThenActive =
          makeAnd(cloneVExpr(Active.get()), cloneVExpr(Cond.get()), I.Loc);
      auto ElseActive = makeAnd(cloneVExpr(Active.get()),
                                makeNot(cloneVExpr(Cond.get()), I.Loc), I.Loc);
      const PassiveTraceKind TraceKind =
          I.IsLoopUnroll ? PassiveTraceKind::Loop : PassiveTraceKind::Branch;
      const std::string ThenMessage =
          I.IsLoopUnroll ? "iteration " + std::to_string(I.LoopUnrollIteration)
                         : "then";
      const std::string ElseMessage =
          I.IsLoopUnroll
              ? "exit after " + std::to_string(I.LoopUnrollIteration == 0
                                                   ? 0
                                                   : I.LoopUnrollIteration - 1)
              : "else";
      emitTrace(TraceKind, ThenMessage, ThenActive.get(), I.Loc);
      emitTrace(TraceKind, ElseMessage, ElseActive.get(), I.Loc);
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
        if (auto Entry = EntryRenames.find(Name); Entry != EntryRenames.end())
          emitInactiveFrame(P, Entry->second, Merged, Ty, EntryActive.get(),
                            I.Loc);
      }
      Active = makeOr(std::move(ThenActive), std::move(ElseActive), I.Loc);
      break;
    }
    case VStmt::Return: {
      const auto &R = static_cast<const VReturnStmt &>(S);
      CloneCtx Ctx{Renames, OldState, false};
      ReturnGuards.push_back(cloneVExpr(Active.get()));
      if (!R.Value) {
        emitTrace(PassiveTraceKind::Return, "return", Active.get(), R.Loc);
        Active = makeBoolLiteral(false, R.Loc);
        break;
      }
      auto BoundReturn = cloneExpr(R.Value.get(), Ctx);
      std::vector<PassiveTraceValue> TraceValues;
      TraceValues.push_back({"value", cloneVExpr(BoundReturn.get())});
      emitTrace(PassiveTraceKind::Return, "return", Active.get(), R.Loc,
                std::move(TraceValues));
      emitExprSafety(P, BoundReturn.get(), Active.get(), R.Loc, Renames, true,
                     R.Value.get());
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
      emitTrace(PassiveTraceKind::Loop, "entry", Active.get(), W.Loc);
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
        emitExprSafety(P, BoundInv.get(), Active.get(), W.Loc, Renames, false,
                       Inv.get());
        emitPassive(P, PassiveStmt::Assert, std::move(BoundInv), Active.get(),
                    W.Loc);
      }

      std::set<std::string> Modified;
      for (const auto &Body : W.Body)
        collectModified(*Body, Modified);
      for (const std::string &Name : Modified) {
        auto Previous = Renames.find(Name);
        if (Previous == Renames.end())
          continue;
        const std::string PreviousName = Previous->second;
        const std::string HeadName = bump(Name);
        Renames[Name] = HeadName;
        emitInactiveFrame(P, PreviousName, HeadName, typeForName(Name),
                          Active.get(), W.Loc);
      }

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
      std::vector<PassiveTraceValue> IterationValues;
      IterationValues.push_back({"condition", cloneVExpr(HeadCond.get())});
      emitTrace(PassiveTraceKind::Loop, "inductive iteration",
                IterationActive.get(), W.Loc, std::move(IterationValues));
      emitExprSafety(P, HeadCond.get(), Active.get(), W.Loc, Renames, false,
                     W.Cond.get());
      emitPassive(P, PassiveStmt::Assume, cloneVExpr(HeadCond.get()),
                  IterationActive.get(), W.Loc);

      std::vector<std::unique_ptr<VExpr>> OldDecreases;
      for (const auto &Decrease : W.Decreases) {
        auto Bound = cloneExpr(Decrease.get(), HeadCtx);
        emitExprSafety(P, Bound.get(), IterationActive.get(), W.Loc, Renames,
                       false, Decrease.get());
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
        emitExprSafety(P, BoundInv.get(), BodyActive.get(), W.Loc, BodyRenames,
                       false, Inv.get());
        emitPassive(P, PassiveStmt::Assert, std::move(BoundInv),
                    BodyActive.get(), W.Loc);
      }

      if (!W.Decreases.empty()) {
        CloneCtx AfterCtx{BodyRenames, OldState, false};
        std::vector<std::unique_ptr<VExpr>> NewDecreases;
        for (const auto &Decrease : W.Decreases) {
          auto Bound = cloneExpr(Decrease.get(), AfterCtx);
          emitExprSafety(P, Bound.get(), BodyActive.get(), W.Loc, BodyRenames,
                         false, Decrease.get());
          NewDecreases.push_back(std::move(Bound));
        }
        emitPassive(P, PassiveStmt::Assert,
                    buildLexDecrease(NewDecreases, OldDecreases, W.Loc),
                    BodyActive.get(), W.Loc);
      }

      emitTrace(PassiveTraceKind::Loop, "exit", Active.get(), W.Loc);
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
      emitExprSafety(P, Cond.get(), Active.get(), A.Loc, Renames, false,
                     A.Cond.get());
      emitPassive(P, PassiveStmt::Assert, std::move(Cond), Active.get(), A.Loc);
      break;
    }
    case VStmt::RevealWithFuel:
    case VStmt::HideSpec:
    case VStmt::RevealSpec:
      break;
    case VStmt::Call: {
      const auto &Call = static_cast<const VCallStmt &>(S);
      CloneCtx TraceCtx{Renames, OldState, false};
      std::vector<PassiveTraceValue> TraceValues;
      for (unsigned I = 0; I != Call.Args.size(); ++I)
        TraceValues.push_back({"arg" + std::to_string(I),
                               cloneExpr(Call.Args[I].get(), TraceCtx)});
      emitTrace(PassiveTraceKind::Call, Call.Callee, Active.get(), Call.Loc,
                std::move(TraceValues));
      const auto EntryRenames = Renames;
      PassiveProgram CallP;
      emitCallStmt(Call, CallP, Renames);
      for (auto &CallStmt : CallP.Stmts) {
        if (CallStmt->Cond)
          CallStmt->Cond = makeImplies(cloneVExpr(Active.get()),
                                       std::move(CallStmt->Cond), S.Loc);
        P.Stmts.push_back(std::move(CallStmt));
      }
      for (const std::string &Heap : HeapBases) {
        auto Before = EntryRenames.find(Heap);
        auto After = Renames.find(Heap);
        if (Before != EntryRenames.end() && After != Renames.end())
          emitInactiveFrame(P, Before->second, After->second, VType::makePtr(),
                            Active.get(), S.Loc);
      }
      break;
    }
    case VStmt::Assert: {
      const auto &A = static_cast<const VAssertStmt &>(S);
      CloneCtx Ctx{Renames, OldState, false};
      auto Cond = cloneExpr(A.Cond.get(), Ctx);
      emitExprSafety(P, Cond.get(), Active.get(), A.Loc, Renames, false,
                     A.Cond.get());
      emitPassive(P, PassiveStmt::Assert, std::move(Cond), Active.get(), A.Loc,
                  A.ProofKind);
      break;
    }
    case VStmt::Assume: {
      const auto &A = static_cast<const VAssumeStmt &>(S);
      CloneCtx Ctx{Renames, OldState, false};
      auto Cond = cloneExpr(A.Cond.get(), Ctx);
      emitExprSafety(P, Cond.get(), Active.get(), A.Loc, Renames, false,
                     A.Cond.get());
      emitPassive(P, PassiveStmt::Assume, std::move(Cond), Active.get(), A.Loc);
      break;
    }
    case VStmt::Seq:
      for (const auto &Nested : static_cast<const VSeqStmt &>(S).Stmts)
        processStmt(*Nested, P, Renames, Active);
      break;
    case VStmt::Havoc: {
      const auto &H = static_cast<const VHavocStmt &>(S);
      const std::string PreviousName = Renames[H.Target];
      const std::string NewName = bump(H.Target);
      Renames[H.Target] = NewName;
      emitInactiveFrame(P, PreviousName, NewName, Types[H.Target], Active.get(),
                        H.Loc);
      break;
    }
    }
  }
};

PassiveProgram Passivizer::run(const VFunction &Fn) {
  PassivizerImpl Impl(Fn, FnMap);
  return Impl.run();
}