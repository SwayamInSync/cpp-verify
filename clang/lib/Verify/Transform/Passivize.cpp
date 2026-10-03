//===--- Passivize.cpp ----------------------------------------------------===//
#include "Passivize.h"
#include "Origins.h"
#include "SpecInline.h"
#include "UBChecks.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/STLFunctionalExtras.h"
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
    if (Ctx.BoundVars.count(Name)) {
      auto Copy = std::make_unique<VVarExpr>(Name, V->Ty, V->Loc,
                                             V->ProvenanceVariable);
      Copy->Origins = V->Origins;
      Copy->OriginCompanion = V->OriginCompanion;
      return Copy;
    }
    if (Ctx.UseOldState) {
      if (auto It = Ctx.OldState.find(Name); It != Ctx.OldState.end())
        return cloneExpr(It->second.get(), CloneCtx{Ctx.Renames, Ctx.OldState,
                                                    false, Ctx.BoundVars});
    }
    if (auto It = Ctx.Renames.find(Name); It != Ctx.Renames.end())
      Name = It->second;
    auto Copy = std::make_unique<VVarExpr>(
        Name, V->Ty, V->Loc, stateVariableName(Ctx, V->ProvenanceVariable));
    Copy->Origins = V->Origins;
    Copy->OriginCompanion = V->OriginCompanion;
    return Copy;
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
                                       C->FromTy, C->Ty, C->Loc, C->IsTrigger);
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
    // A heap-reading call is evaluated in the heap state a load would read.
    std::string Heap;
    if (C->ReadsHeap) {
      Heap = Ctx.Renames.count(VHeapName) ? Ctx.Renames.at(VHeapName)
                                          : std::string(VHeapName) + "_0";
      if (Ctx.UseOldState) {
        if (auto HIt = Ctx.OldState.find(VHeapName);
            HIt != Ctx.OldState.end()) {
          if (const auto *HV = static_cast<const VVarExpr *>(HIt->second.get()))
            Heap = HV->Name;
        }
      } else if (!C->HeapVar.empty()) {
        Heap = C->HeapVar;
      }
    }
    return std::make_unique<VSpecCallExpr>(C->Callee, C->CalleeIdentity,
                                           std::move(Args), C->Ty, C->Loc,
                                           C->ReadsHeap, std::move(Heap));
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
  case VExpr::HeapFrame: {
    const auto *H = static_cast<const VHeapFrameExpr *>(E);
    std::vector<std::pair<std::unique_ptr<VExpr>, std::unique_ptr<VExpr>>>
        Regions;
    for (const auto &[Lo, Hi] : H->Regions)
      Regions.emplace_back(cloneExpr(Lo.get(), Ctx), cloneExpr(Hi.get(), Ctx));
    return std::make_unique<VHeapFrameExpr>(H->HeapBefore, H->HeapAfter,
                                            std::move(Regions), H->Loc);
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

static bool isFalseLiteral(const VExpr *E) {
  if (!E || E->K != VExpr::Literal || E->Ty.Kind != VTypeKind::Bool)
    return false;
  return static_cast<const VLiteralExpr *>(E)->Value == "0";
}

static std::unique_ptr<VExpr>
buildLexDecrease(const std::vector<std::unique_ptr<VExpr>> &NewValues,
                 const std::vector<std::unique_ptr<VExpr>> &OldValues,
                 SourceLocation Loc) {
  if (NewValues.empty() || NewValues.size() != OldValues.size())
    return makeBoolLiteral(false, Loc);

  // Only the deciding component has to be nonnegative, and only before the
  // step (ACSL's loop variant).
  std::unique_ptr<VExpr> LexLess = makeBoolLiteral(false, Loc);
  for (size_t J = 0; J < NewValues.size(); ++J) {
    if (!NewValues[J] || !OldValues[J])
      return makeBoolLiteral(false, Loc);
    std::unique_ptr<VExpr> Disjunct =
        makeAnd(std::make_unique<VBinOpExpr>(
                    VBinOp::Ge, cloneVExpr(OldValues[J].get()),
                    std::make_unique<VLiteralExpr>(0, OldValues[J]->Ty, Loc),
                    VType::makeBool(), Loc),
                std::make_unique<VBinOpExpr>(
                    VBinOp::Lt, cloneVExpr(NewValues[J].get()),
                    cloneVExpr(OldValues[J].get()), VType::makeBool(), Loc),
                Loc);
    for (size_t I = 0; I < J; ++I)
      Disjunct =
          makeAnd(std::make_unique<VBinOpExpr>(
                      VBinOp::Eq, cloneVExpr(NewValues[I].get()),
                      cloneVExpr(OldValues[I].get()), VType::makeBool(), Loc),
                  std::move(Disjunct), Loc);
    LexLess = makeOr(std::move(LexLess), std::move(Disjunct), Loc);
  }
  return LexLess;
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

/// One definedness check and the obligation kind it becomes.
struct SafetyCheck {
  ProofObligationKind Kind;
  std::unique_ptr<VExpr> Cond;
  std::string Note = {};
};
using SafetyChecks = std::vector<SafetyCheck>;

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

/// A mathematical value converted to a machine type must be representable.
static std::unique_ptr<VExpr> mathValueFits(const VCastExpr *C) {
  const VType &To = C->Ty;
  if (To.BitWidth == 0)
    return makeBoolLiteral(false, C->Loc);
  llvm::APInt Min = To.IsSigned ? llvm::APInt::getSignedMinValue(To.BitWidth)
                                : llvm::APInt::getMinValue(To.BitWidth);
  llvm::APInt Max = To.IsSigned ? llvm::APInt::getSignedMaxValue(To.BitWidth)
                                : llvm::APInt::getMaxValue(To.BitWidth);
  VType LimitTy = VType::makeInt(VIntMode::Math, To.BitWidth + 1, true);
  auto Limit = [&](const llvm::APInt &Value) {
    llvm::SmallString<64> Buffer;
    Value.toString(Buffer, 10, To.IsSigned);
    return std::make_unique<VLiteralExpr>(std::string(Buffer), LimitTy, C->Loc);
  };
  auto AtLeast =
      std::make_unique<VBinOpExpr>(VBinOp::Ge, cloneVExpr(C->Inner.get()),
                                   Limit(Min), VType::makeBool(), C->Loc);
  auto AtMost =
      std::make_unique<VBinOpExpr>(VBinOp::Le, cloneVExpr(C->Inner.get()),
                                   Limit(Max), VType::makeBool(), C->Loc);
  return makeAnd(std::move(AtLeast), std::move(AtMost), C->Loc);
}

static std::unique_ptr<VExpr> mathCast(const VExpr *E);

/// The converted value lies in the target enumeration's value range.
static std::unique_ptr<VExpr> enumValueInRange(const VCastExpr *C) {
  const VExpr *Inner = C->Inner.get();
  VType MathTy = VType::makeInt(VIntMode::Math, 64, true);
  std::unique_ptr<VExpr> Value;
  if (Inner->Ty.Kind == VTypeKind::Bool) {
    Value = std::make_unique<VConditionalExpr>(
        cloneVExpr(Inner), std::make_unique<VLiteralExpr>(1, MathTy, C->Loc),
        std::make_unique<VLiteralExpr>(0, MathTy, C->Loc), MathTy, C->Loc);
  } else if (Inner->Ty.IntMode == VIntMode::Math) {
    Value = cloneVExpr(Inner);
  } else {
    Value = mathCast(Inner);
  }
  auto AtLeast = std::make_unique<VBinOpExpr>(
      VBinOp::Ge, cloneVExpr(Value.get()),
      std::make_unique<VLiteralExpr>(C->Ty.EnumMin, MathTy, C->Loc),
      VType::makeBool(), C->Loc);
  auto Below = std::make_unique<VBinOpExpr>(
      VBinOp::Lt, std::move(Value),
      std::make_unique<VLiteralExpr>(C->Ty.EnumMax, MathTy, C->Loc),
      VType::makeBool(), C->Loc);
  return makeAnd(std::move(AtLeast), std::move(Below), C->Loc);
}

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
  const VType &RhsTy = B->Rhs->Ty;
  if (RhsTy.Kind == Ty.Kind && RhsTy.IntMode == Ty.IntMode &&
      RhsTy.IsSigned == Ty.IsSigned && RhsTy.BitWidth == Ty.BitWidth &&
      (B->Op == VBinOp::Add || B->Op == VBinOp::Sub || B->Op == VBinOp::Mul))
    return std::make_unique<VOverflowCheckExpr>(
        B->Op == VBinOp::Add   ? VOverflowOp::Add
        : B->Op == VBinOp::Sub ? VOverflowOp::Sub
                               : VOverflowOp::Mul,
        cloneVExpr(B->Lhs.get()), cloneVExpr(B->Rhs.get()), B->Loc);
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

/// Pointer lies in the closed byte range of the object its origin names:
/// a parameter's entry object (its declared extent, else one element) or a
/// global. Null when an origin is not such an object.
static std::unique_ptr<VExpr>
originPositionSafety(const VExpr *Pointer,
                     const std::vector<VValidExtent> &Extents,
                     SourceLocation Loc) {
  auto Origins = pointerOrigins(Pointer);
  const uint64_t Stride = Pointer->Ty.PointeeSizeBytes;
  if (!Origins || Origins->empty() || Stride == 0 ||
      hasPointerProvenance(Pointer))
    return nullptr;
  auto Term = Origins->size() > 1 ? pointerOriginTerm(Pointer) : nullptr;
  if (Origins->size() > 1 && !Term)
    return nullptr;
  std::unique_ptr<VExpr> Any = makeBoolLiteral(false, Loc);
  for (const std::string &Origin : *Origins) {
    std::unique_ptr<VExpr> Start;
    std::unique_ptr<VExpr> Bytes;
    if (isGlobalOrigin(Origin)) {
      auto [Address, Size] = globalOriginExtent(Origin);
      Start = std::make_unique<VLiteralExpr>(Address, Pointer->Ty, Loc);
      Bytes = std::make_unique<VLiteralExpr>(std::to_string(Size),
                                             pointerOffsetType(), Loc);
    } else {
      VType PointerType = Pointer->Ty;
      Start = std::make_unique<VOldExpr>(
          std::make_unique<VVarExpr>(Origin, PointerType, Loc), PointerType,
          Loc);
      const VValidExtent *Extent = nullptr;
      for (const VValidExtent &Candidate : Extents)
        if (Candidate.Base == Origin)
          Extent = &Candidate;
      if (Extent && Extent->PointerType.PointeeSizeBytes != Stride)
        return nullptr;
      if (Extent) {
        VOldExpr Length(cloneVExpr(Extent->Length.get()), Extent->Length->Ty,
                        Loc);
        Bytes = scaledExtent(&Length, Stride, Loc);
      } else {
        Bytes = std::make_unique<VLiteralExpr>(std::to_string(Stride),
                                               pointerOffsetType(), Loc);
      }
      if (!Bytes)
        return nullptr;
    }
    auto End =
        std::make_unique<VBinOpExpr>(VBinOp::Add, cloneVExpr(Start.get()),
                                     std::move(Bytes), Pointer->Ty, Loc);
    auto In = makeAnd(
        std::make_unique<VBinOpExpr>(VBinOp::Le, std::move(Start),
                                     cloneVExpr(Pointer), VType::makeBool(),
                                     Loc),
        std::make_unique<VBinOpExpr>(VBinOp::Le, cloneVExpr(Pointer),
                                     std::move(End), VType::makeBool(), Loc),
        Loc);
    if (Term)
      In = makeAnd(
          makeEq(cloneVExpr(Term.get()), originIdentity(Origin, Loc), Loc),
          std::move(In), Loc);
    Any = makeOr(std::move(Any), std::move(In), Loc);
  }
  return Any;
}

static std::unique_ptr<VExpr> pointerPositionSafety(
    const VExpr *Pointer, const std::vector<VValidExtent> *ValidExtents,
    const std::set<std::string> *PointerParams,
    const std::vector<VValidExtent> *OriginExtents, SourceLocation Loc) {
  if (OriginExtents)
    if (auto ByOrigin = originPositionSafety(Pointer, *OriginExtents, Loc))
      return ByOrigin;
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
  case VExpr::HeapFrame:
    for (const auto &[Lo, Hi] : static_cast<const VHeapFrameExpr *>(E)->Regions)
      if (referencesVar(Lo.get(), Name) || referencesVar(Hi.get(), Name))
        return true;
    return false;
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
  case VExpr::HeapFrame:
    return false;
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
  case VStmt::Assert: {
    // Bounds instrumentation checks the callee's own object and has no
    // effect on what the caller passes.
    const auto &A = static_cast<const VAssertStmt &>(S);
    return A.ProofKind == ProofObligationKind::Bounds ||
           scalarDynamicExprSafe(A.Cond.get(), Aliases);
  }
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
  case VStmt::Break:
  case VStmt::Continue:
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
  // A generated validity postcondition states where the result lies, which
  // does not use the pointer.
  for (size_t I = 0; I != Fn.Postconditions.size(); ++I)
    if (postconditionKind(Fn, I) != ProofObligationKind::PointerValidity &&
        !scalarDynamicExprSafe(Fn.Postconditions[I].get(), Aliases))
      Safe = false;
  for (const VFootprint &F : Fn.Modifies)
    if (!scalarDynamicExprSafe(F.Target.get(), Aliases) ||
        (F.Count && !scalarDynamicExprSafe(F.Count.get(), Aliases)))
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

/// The obligation that two pointers being subtracted address one object.
/// Local and dynamic storage carries its lifetime identity, so a mismatch
/// there is a pointer-difference error. Pointers into the objects of
/// parameters or globals have the origins annotatePointerOrigins found;
/// different origins may still lie in one caller array, which the object
/// model does not describe, so that requirement is unsupported, not an
/// error.
static constexpr const char *DifferentObjectsNote =
    "the operands of this pointer difference may address the objects of "
    "different parameters or globals, which may be one caller array; "
    "contracts cannot state that";
static constexpr const char *UnknownOriginNote =
    "an operand of this pointer difference was loaded from memory or "
    "returned by a call, so the object it addresses is not known";

static std::pair<ProofObligationKind, std::unique_ptr<VExpr>>
samePointerDifferenceOrigin(const VExpr *L, const VExpr *R,
                            SourceLocation Loc) {
  auto LProvenance = pointerProvenance(L);
  auto RProvenance = pointerProvenance(R);
  if (LProvenance && RProvenance)
    return {ProofObligationKind::PointerDifference,
            makeEq(std::move(LProvenance), std::move(RProvenance), Loc)};
  if (LProvenance || RProvenance)
    return {ProofObligationKind::PointerDifference,
            makeBoolLiteral(false, Loc)};

  const VExpr *LBase = pointerBase(L);
  const VExpr *RBase = pointerBase(R);
  if (LBase && RBase && LBase->K == VExpr::Var && RBase->K == VExpr::Var &&
      static_cast<const VVarExpr *>(LBase)->Name ==
          static_cast<const VVarExpr *>(RBase)->Name)
    return {ProofObligationKind::PointerDifference, makeBoolLiteral(true, Loc)};
  auto LOrigin = pointerOriginTerm(L);
  auto ROrigin = pointerOriginTerm(R);
  if (!LOrigin || !ROrigin)
    return {ProofObligationKind::Unsupported, makeBoolLiteral(false, Loc)};
  if (LOrigin->K == VExpr::Literal && ROrigin->K == VExpr::Literal)
    return {
        ProofObligationKind::Unsupported,
        makeBoolLiteral(static_cast<const VLiteralExpr &>(*LOrigin).Value ==
                            static_cast<const VLiteralExpr &>(*ROrigin).Value,
                        Loc)};
  return {ProofObligationKind::Unsupported,
          makeEq(std::move(LOrigin), std::move(ROrigin), Loc)};
}

/// Whether a footprint is the whole object its pointer addresses, rather
/// than one cell or a range of cells.
static bool isRegionFootprint(const VFootprint &F,
                              const std::set<std::string> &ReferenceParams) {
  if (F.Count)
    return false;
  const VExpr *E = F.Target.get();
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
  for (const VFootprint &Modify : Fn.Modifies) {
    if (!Modify.Target || Modify.Target->K != VExpr::Load ||
        !isRegionFootprint(Modify, Fn.ReferenceParams))
      continue;
    const VExpr *Ptr = pointerBase(
        static_cast<const VLoadExpr *>(Modify.Target.get())->Ptr.get());
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
  case VStmt::Break:
  case VStmt::Continue:
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
    HasPointerParam |= Param.second.Kind == VTypeKind::Ptr &&
                       !Fn.ConstAddressParams.count(Param.first);
  if (!HasPointerParam)
    return false;
  std::set<std::string> Active;
  return functionMayWriteHeap(Fn, FnMap, Active);
}

/// A global variable's fixed address: its cell is always accessible and
/// initialized.
static bool isGlobalCell(const VExpr *Base) {
  return Base && Base->K == VExpr::Literal && Base->Ty.Kind == VTypeKind::Ptr &&
         static_cast<const VLiteralExpr *>(Base)->Value != "0";
}

/// Storage that is not a global lies at a positive address below the
/// globals.
static std::unique_ptr<VExpr> belowGlobals(const VExpr *Pointer,
                                           uint64_t SizeBytes,
                                           SourceLocation Loc) {
  auto End = std::make_unique<VBinOpExpr>(
      VBinOp::Add, cloneVExpr(Pointer),
      std::make_unique<VLiteralExpr>(std::to_string(SizeBytes),
                                     pointerOffsetType(), Loc),
      VType::makePtr(), Loc);
  auto Positive = std::make_unique<VBinOpExpr>(
      VBinOp::Lt, std::make_unique<VLiteralExpr>(0, VType::makePtr(), Loc),
      cloneVExpr(Pointer), VType::makeBool(), Loc);
  auto Below = std::make_unique<VBinOpExpr>(
      VBinOp::Le, std::move(End),
      std::make_unique<VLiteralExpr>(std::to_string(GlobalRegionBase),
                                     VType::makePtr(), Loc),
      VType::makeBool(), Loc);
  return std::make_unique<VBinOpExpr>(VBinOp::And, std::move(Positive),
                                      std::move(Below), VType::makeBool(), Loc);
}

/// In the object model a pointer without provenance needs only to be
/// non-null here: its access is checked against the parameters' objects.
static std::unique_ptr<VExpr> nonNullSafety(const VExpr *Ptr,
                                            SourceLocation Loc,
                                            bool ObjectModel = false) {
  const VExpr *Base = pointerBase(Ptr);
  if (!Base)
    return makeBoolLiteral(false, Loc);
  if (isGlobalCell(Base))
    return makeBoolLiteral(true, Loc);
  const VExpr *CheckedPointer = hasPointerProvenance(Ptr) ? Ptr : Base;
  auto NonNull = std::make_unique<VBinOpExpr>(
      VBinOp::Ne, cloneVExpr(CheckedPointer),
      std::make_unique<VLiteralExpr>(0, VType::makePtr(), Loc),
      VType::makeBool(), Loc);
  if (ObjectModel && !hasPointerProvenance(Ptr))
    return NonNull;
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
                                                SourceLocation Loc,
                                                bool ObjectModel = false) {
  const VExpr *Base = pointerBase(Ptr);
  if (!Base)
    return makeBoolLiteral(false, Loc);
  if (isGlobalCell(Base))
    return makeBoolLiteral(true, Loc);
  // Abstract storage is initialized.
  if (ObjectModel && !hasPointerProvenance(Ptr))
    return makeBoolLiteral(true, Loc);
  const VExpr *CheckedPointer = hasPointerProvenance(Ptr) ? Ptr : Base;
  return std::make_unique<VUnaryOpExpr>(VUnaryOp::InitializedPtr,
                                        cloneVExpr(CheckedPointer),
                                        VType::makeBool(), Loc);
}

static void addSafety(SafetyChecks &Out, ProofObligationKind Kind,
                      std::unique_ptr<VExpr> Cond, SourceLocation Loc,
                      std::string Note = "") {
  if (!Cond)
    Cond = makeBoolLiteral(false, Loc);
  if (Cond->K == VExpr::Literal && Cond->Ty.Kind == VTypeKind::Bool &&
      static_cast<const VLiteralExpr &>(*Cond).Value == "1")
    return;
  Out.push_back({Kind, std::move(Cond), std::move(Note)});
}

/// One conjunction per kind, in order of first occurrence, so an expression
/// yields at most one obligation of each kind.
static void groupByKind(SafetyChecks &Checks) {
  SafetyChecks Grouped;
  for (SafetyCheck &Check : Checks) {
    auto Same = llvm::find_if(Grouped, [&](const SafetyCheck &Existing) {
      return Existing.Kind == Check.Kind;
    });
    if (Same == Grouped.end()) {
      Grouped.push_back(std::move(Check));
      continue;
    }
    const SourceLocation Loc = Same->Cond->Loc;
    Same->Cond =
        combineSafety(std::move(Same->Cond), std::move(Check.Cond), Loc);
    if (Same->Note.empty())
      Same->Note = std::move(Check.Note);
  }
  Checks = std::move(Grouped);
}

static void appendGuardedSafety(SafetyChecks &Out, SafetyChecks Checks,
                                const VExpr *Guard, SourceLocation Loc) {
  groupByKind(Checks);
  for (SafetyCheck &Check : Checks)
    Out.push_back({Check.Kind,
                   makeImplies(cloneVExpr(Guard), std::move(Check.Cond), Loc),
                   std::move(Check.Note)});
}

static void
collectSafety(const VExpr *E, const FunctionMap *FnMap,
              const std::vector<VValidExtent> *ValidExtents,
              const std::set<std::string> *PointerParams, SafetyChecks &Out,
              bool ObjectModel = false,
              const std::vector<VValidExtent> *OriginExtents = nullptr) {
  auto Collect = [&](const VExpr *Sub, SafetyChecks &Into) {
    collectSafety(Sub, FnMap, ValidExtents, PointerParams, Into, ObjectModel,
                  OriginExtents);
  };
  if (!E) {
    addSafety(Out, ProofObligationKind::Unsupported, nullptr, SourceLocation(),
              "an expression the verifier could not lower");
    return;
  }
  switch (E->K) {
  case VExpr::Literal:
  case VExpr::Var:
  case VExpr::Result:
    return;
  case VExpr::BinOp: {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    Collect(B->Lhs.get(), Out);
    SafetyChecks Right;
    Collect(B->Rhs.get(), Right);
    if (B->Op == VBinOp::And) {
      appendGuardedSafety(Out, std::move(Right), B->Lhs.get(), B->Loc);
      return;
    }
    if (B->Op == VBinOp::Or) {
      auto LhsFalse = makeNot(cloneVExpr(B->Lhs.get()), B->Loc);
      appendGuardedSafety(Out, std::move(Right), LhsFalse.get(), B->Loc);
      return;
    }
    for (SafetyCheck &Check : Right)
      Out.push_back(std::move(Check));
    if (B->Op == VBinOp::Sub && B->Lhs->Ty.Kind == VTypeKind::Ptr &&
        B->Rhs->Ty.Kind == VTypeKind::Ptr) {
      const VExpr *LeftBase = pointerBase(B->Lhs.get());
      const VExpr *RightBase = pointerBase(B->Rhs.get());
      addSafety(Out, ProofObligationKind::PointerDifference,
                makeAnd(nonNullSafety(LeftBase, B->Loc, ObjectModel),
                        nonNullSafety(RightBase, B->Loc, ObjectModel), B->Loc),
                B->Loc);
      auto [OriginKind, SameOrigin] =
          samePointerDifferenceOrigin(B->Lhs.get(), B->Rhs.get(), B->Loc);
      const bool Known =
          pointerOriginTerm(B->Lhs.get()) && pointerOriginTerm(B->Rhs.get());
      addSafety(Out, OriginKind, std::move(SameOrigin), B->Loc,
                OriginKind != ProofObligationKind::Unsupported ? ""
                : Known ? DifferentObjectsNote
                        : UnknownOriginNote);
      addSafety(Out, ProofObligationKind::Bounds,
                pointerPositionSafety(B->Lhs.get(), ValidExtents, PointerParams,
                                      OriginExtents, B->Loc),
                B->Loc);
      addSafety(Out, ProofObligationKind::Bounds,
                pointerPositionSafety(B->Rhs.get(), ValidExtents, PointerParams,
                                      OriginExtents, B->Loc),
                B->Loc);
    }
    if (B->Op == VBinOp::Shl || B->Op == VBinOp::Shr) {
      addSafety(Out, ProofObligationKind::Shift, shiftSafety(B), B->Loc);
      return;
    }
    // A mathematical operand makes the whole operation mathematical.
    const bool MachineOperation =
        evaluatedIntMode(B->Lhs.get()) == VIntMode::Machine &&
        evaluatedIntMode(B->Rhs.get()) == VIntMode::Machine;
    if (B->Op == VBinOp::Add || B->Op == VBinOp::Sub || B->Op == VBinOp::Mul) {
      if (MachineOperation)
        addSafety(Out, ProofObligationKind::Overflow, signedArithmeticSafety(B),
                  B->Loc);
      return;
    }
    // Only a spec body divides totally; evaluated C++ division needs a
    // nonzero divisor whatever the operands' modes.
    if ((B->Op == VBinOp::Div || B->Op == VBinOp::Rem) &&
        B->Ty.IntMode == VIntMode::Machine) {
      addSafety(Out, ProofObligationKind::DivisionByZero,
                std::make_unique<VBinOpExpr>(
                    VBinOp::Ne, cloneVExpr(B->Rhs.get()),
                    std::make_unique<VLiteralExpr>(0, B->Rhs->Ty, B->Loc),
                    VType::makeBool(), B->Loc),
                B->Loc);
      if (MachineOperation && isSignedMachineInteger(B->Lhs->Ty) &&
          B->Lhs->Ty.BitWidth != 0) {
        auto IsMin = std::make_unique<VBinOpExpr>(
            VBinOp::Eq, cloneVExpr(B->Lhs.get()),
            std::make_unique<VLiteralExpr>(
                signedLimit(B->Lhs->Ty.BitWidth, true), B->Lhs->Ty, B->Loc),
            VType::makeBool(), B->Loc);
        auto IsMinusOne = std::make_unique<VBinOpExpr>(
            VBinOp::Eq, cloneVExpr(B->Rhs.get()),
            std::make_unique<VLiteralExpr>(-1, B->Rhs->Ty, B->Loc),
            VType::makeBool(), B->Loc);
        addSafety(
            Out, ProofObligationKind::Overflow,
            makeNot(makeAnd(std::move(IsMin), std::move(IsMinusOne), B->Loc),
                    B->Loc),
            B->Loc);
      }
    }
    return;
  }
  case VExpr::UnaryOp: {
    const auto *U = static_cast<const VUnaryOpExpr *>(E);
    Collect(U->Operand.get(), Out);
    if (U->Op != VUnaryOp::Neg || !isSignedMachineInteger(U->Operand->Ty) ||
        evaluatedIntMode(U->Operand.get()) == VIntMode::Math ||
        U->Operand->Ty.BitWidth == 0)
      return;
    addSafety(Out, ProofObligationKind::Overflow,
              std::make_unique<VBinOpExpr>(
                  VBinOp::Ne, cloneVExpr(U->Operand.get()),
                  std::make_unique<VLiteralExpr>(
                      signedLimit(U->Operand->Ty.BitWidth, true),
                      U->Operand->Ty, U->Loc),
                  VType::makeBool(), U->Loc),
              U->Loc);
    return;
  }
  case VExpr::Cast: {
    const auto *C = static_cast<const VCastExpr *>(E);
    Collect(C->Inner.get(), Out);
    if (loweredPointerDifferenceQuotient(C))
      addSafety(Out, ProofObligationKind::Overflow,
                pointerDifferenceRepresentability(C), C->Loc);
    if (isIntegerType(C->Inner->Ty) &&
        evaluatedIntMode(C->Inner.get()) == VIntMode::Math &&
        isIntegerType(C->Ty) && C->Ty.IntMode == VIntMode::Machine)
      addSafety(Out, ProofObligationKind::Overflow, mathValueFits(C), C->Loc);
    if (!C->Ty.EnumMin.empty() && (C->FromTy.EnumMin != C->Ty.EnumMin ||
                                   C->FromTy.EnumMax != C->Ty.EnumMax))
      addSafety(Out, ProofObligationKind::Overflow, enumValueInRange(C),
                C->Loc);
    return;
  }
  case VExpr::Load: {
    const auto *L = static_cast<const VLoadExpr *>(E);
    Collect(L->Ptr.get(), Out);
    addSafety(Out, ProofObligationKind::Dereference,
              nonNullSafety(L->Ptr.get(), L->Loc, ObjectModel), L->Loc);
    addSafety(Out, ProofObligationKind::Initialization,
              initializedSafety(L->Ptr.get(), L->Loc, ObjectModel), L->Loc);
    if (L->AccessCondition)
      addSafety(Out, ProofObligationKind::Bounds,
                cloneVExpr(L->AccessCondition.get()), L->Loc);
    return;
  }
  case VExpr::Old: {
    SafetyChecks Inner;
    Collect(static_cast<const VOldExpr *>(E)->Inner.get(), Inner);
    groupByKind(Inner);
    for (SafetyCheck &Check : Inner)
      Out.push_back(
          {Check.Kind, std::make_unique<VOldExpr>(std::move(Check.Cond),
                                                  VType::makeBool(), E->Loc)});
    return;
  }
  case VExpr::Conditional: {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    Collect(C->Cond.get(), Out);
    SafetyChecks Then;
    Collect(C->Then.get(), Then);
    appendGuardedSafety(Out, std::move(Then), C->Cond.get(), C->Loc);
    SafetyChecks Else;
    Collect(C->Else.get(), Else);
    auto CondFalse = makeNot(cloneVExpr(C->Cond.get()), C->Loc);
    appendGuardedSafety(Out, std::move(Else), CondFalse.get(), C->Loc);
    return;
  }
  case VExpr::OverflowCheck: {
    const auto *O = static_cast<const VOverflowCheckExpr *>(E);
    Collect(O->Lhs.get(), Out);
    if (O->Rhs)
      Collect(O->Rhs.get(), Out);
    return;
  }
  case VExpr::Forall:
  case VExpr::Exists: {
    const auto *Q = static_cast<const VQuantifiedExpr *>(E);
    if (Q->Lo) {
      Collect(Q->Lo.get(), Out);
      Collect(Q->Hi.get(), Out);
    }
    SafetyChecks Body;
    Collect(Q->Body.get(), Body);
    groupByKind(Body);
    for (SafetyCheck &Check : Body)
      Out.push_back(
          {Check.Kind,
           std::make_unique<VForallExpr>(
               Q->Binder, cloneVExpr(Q->Lo.get()), cloneVExpr(Q->Hi.get()),
               std::move(Check.Cond), Q->Loc, Q->BinderType)});
    return;
  }
  case VExpr::HeapStore: {
    const auto *H = static_cast<const VHeapStoreExpr *>(E);
    Collect(H->Ptr.get(), Out);
    Collect(H->Val.get(), Out);
    addSafety(Out, ProofObligationKind::Dereference,
              nonNullSafety(H->Ptr.get(), H->Loc, ObjectModel), H->Loc);
    return;
  }
  case VExpr::HeapFrame:
    for (const auto &[Lo, Hi] : static_cast<const VHeapFrameExpr *>(E)->Regions) {
      Collect(Lo.get(), Out);
      Collect(Hi.get(), Out);
    }
    return;
  case VExpr::FieldAccess:
    Collect(static_cast<const VFieldAccessExpr *>(E)->Base.get(), Out);
    return;
  case VExpr::SpecCall: {
    const auto *C = static_cast<const VSpecCallExpr *>(E);
    for (const auto &Arg : C->Args)
      Collect(Arg.get(), Out);
    if (!FnMap)
      return;
    auto It = FnMap->find(C->CalleeIdentity);
    if (It == FnMap->end() || !It->second->RequiresCallDefinedness)
      return;
    if (It->second->NeedsDecreasesCheck) {
      addSafety(Out, ProofObligationKind::Unsupported, nullptr, C->Loc,
                "the C++ definedness of a call of the recursive constexpr "
                "function " +
                    It->second->Name + " is not checked");
      return;
    }
    auto Expanded = SpecInliner(*FnMap, {}).inlineExpr(cloneVExpr(C));
    if (!Expanded || Expanded->K == VExpr::SpecCall) {
      addSafety(Out, ProofObligationKind::Unsupported, nullptr, C->Loc,
                "the call of the constexpr function " + It->second->Name +
                    " could not be unfolded to check its C++ definedness");
      return;
    }
    Collect(Expanded.get(), Out);
    return;
  }
  }
  addSafety(Out, ProofObligationKind::Unsupported, nullptr, E->Loc,
            "an expression whose C++ definedness is not modeled");
}

/// The conjunction of every definedness check of E.
static std::unique_ptr<VExpr>
safetyForExpr(const VExpr *E, const FunctionMap *FnMap,
              const std::vector<VValidExtent> *ValidExtents,
              const std::set<std::string> *PointerParams) {
  SafetyChecks Checks;
  collectSafety(E, FnMap, ValidExtents, PointerParams, Checks);
  const SourceLocation Loc = E ? E->Loc : SourceLocation();
  if (Checks.empty())
    return makeBoolLiteral(true, Loc);
  std::unique_ptr<VExpr> Safe = std::move(Checks.front().Cond);
  for (size_t I = 1; I != Checks.size(); ++I)
    Safe = combineSafety(std::move(Safe), std::move(Checks[I].Cond), Loc);
  return Safe;
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
  case VExpr::HeapFrame: {
    const auto *H = static_cast<const VHeapFrameExpr *>(E);
    std::unique_ptr<VExpr> Bridge = makeBoolLiteral(true, H->Loc);
    for (const auto &[Lo, Hi] : H->Regions) {
      Bridge = combineSafety(std::move(Bridge),
                             machineMathBridgeForExpr(Lo.get(), FnMap, false),
                             H->Loc);
      Bridge = combineSafety(std::move(Bridge),
                             machineMathBridgeForExpr(Hi.get(), FnMap, false),
                             H->Loc);
    }
    return Bridge;
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
  case VExpr::HeapFrame:
    for (const auto &[Lo, Hi] : static_cast<const VHeapFrameExpr *>(E)->Regions) {
      collectDottedVars(Lo.get(), Out);
      collectDottedVars(Hi.get(), Out);
    }
    return;
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
        C->FromTy, C->Ty, C->Loc, C->IsTrigger);
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
    std::string Heap;
    if (C->ReadsHeap)
      Heap = HeapOverride.empty() ? Ctx.Renames.at(VHeapName) : HeapOverride;
    return std::make_unique<VSpecCallExpr>(C->Callee, C->CalleeIdentity,
                                           std::move(Args), C->Ty, C->Loc,
                                           C->ReadsHeap, std::move(Heap));
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
  case VExpr::HeapFrame: {
    const auto *H = static_cast<const VHeapFrameExpr *>(E);
    std::vector<std::pair<std::unique_ptr<VExpr>, std::unique_ptr<VExpr>>>
        Regions;
    for (const auto &[Lo, Hi] : H->Regions)
      Regions.emplace_back(
          substParams(Lo.get(), Map, Ctx, EntryHeap, HeapOverride, BoundVars,
                      OldMap, NormalizedPointerChecks),
          substParams(Hi.get(), Map, Ctx, EntryHeap, HeapOverride, BoundVars,
                      OldMap, NormalizedPointerChecks));
    return std::make_unique<VHeapFrameExpr>(H->HeapBefore, H->HeapAfter,
                                            std::move(Regions), H->Loc);
  }
  }
  return nullptr;
}

/// A structural key of an expression, or false.
static bool expressionKey(const VExpr *E, std::string &Key) {
  if (!E)
    return false;
  Key += '(' + std::to_string(E->K) + ':' +
         std::to_string(static_cast<int>(E->Ty.Kind)) +
         std::to_string(static_cast<int>(E->Ty.IntMode)) +
         std::to_string(E->Ty.IsSigned) + std::to_string(E->Ty.BitWidth);
  switch (E->K) {
  case VExpr::Literal:
    Key += static_cast<const VLiteralExpr *>(E)->Value;
    break;
  case VExpr::Var: {
    Key += static_cast<const VVarExpr *>(E)->Name;
    break;
  }
  case VExpr::BinOp: {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    Key += std::to_string(static_cast<int>(B->Op));
    if (!expressionKey(B->Lhs.get(), Key) || !expressionKey(B->Rhs.get(), Key))
      return false;
    break;
  }
  case VExpr::UnaryOp: {
    const auto *U = static_cast<const VUnaryOpExpr *>(E);
    if (U->Op == VUnaryOp::ValidPtr || U->Op == VUnaryOp::InitializedPtr)
      return false;
    Key += std::to_string(static_cast<int>(U->Op));
    if (!expressionKey(U->Operand.get(), Key))
      return false;
    break;
  }
  case VExpr::Cast: {
    const auto *C = static_cast<const VCastExpr *>(E);
    Key += std::to_string(static_cast<int>(C->FromTy.Kind)) +
           std::to_string(static_cast<int>(C->FromTy.IntMode)) +
           std::to_string(C->FromTy.IsSigned) +
           std::to_string(C->FromTy.BitWidth);
    if (!expressionKey(C->Inner.get(), Key))
      return false;
    break;
  }
  case VExpr::Load: {
    const auto *L = static_cast<const VLoadExpr *>(E);
    if (L->AccessCondition)
      return false;
    Key += L->HeapVar;
    if (!expressionKey(L->Ptr.get(), Key))
      return false;
    break;
  }
  case VExpr::Conditional: {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    if (!expressionKey(C->Cond.get(), Key) ||
        !expressionKey(C->Then.get(), Key) ||
        !expressionKey(C->Else.get(), Key))
      return false;
    break;
  }
  case VExpr::SpecCall: {
    const auto *C = static_cast<const VSpecCallExpr *>(E);
    Key += C->CalleeIdentity + '@' + C->HeapVar;
    for (const auto &Arg : C->Args)
      if (!expressionKey(Arg.get(), Key))
        return false;
    break;
  }
  default:
    return false;
  }
  Key += ')';
  return true;
}

/// An application of a spec with a reads clause, with the quantifiers whose
/// binders it may mention, outermost first.
struct FramedApplication {
  const VSpecCallExpr *Call = nullptr;
  std::vector<const VQuantifiedExpr *> Enclosing;
};

using ApplicationFilter =
    llvm::function_ref<bool(const VSpecCallExpr &, const VFunction &)>;

static void
collectFramedApplications(const VExpr *E, const FunctionMap &FnMap,
                          std::vector<const VQuantifiedExpr *> &Enclosing,
                          std::map<std::string, FramedApplication> &Out,
                          ApplicationFilter Wanted) {
  if (!E)
    return;
  auto visit = [&](const VExpr *Child) {
    collectFramedApplications(Child, FnMap, Enclosing, Out, Wanted);
  };
  switch (E->K) {
  case VExpr::BinOp: {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    visit(B->Lhs.get());
    visit(B->Rhs.get());
    return;
  }
  case VExpr::UnaryOp:
    visit(static_cast<const VUnaryOpExpr *>(E)->Operand.get());
    return;
  case VExpr::Cast:
    visit(static_cast<const VCastExpr *>(E)->Inner.get());
    return;
  case VExpr::Old:
    visit(static_cast<const VOldExpr *>(E)->Inner.get());
    return;
  case VExpr::Load: {
    const auto *L = static_cast<const VLoadExpr *>(E);
    visit(L->Ptr.get());
    visit(L->AccessCondition.get());
    return;
  }
  case VExpr::Conditional: {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    visit(C->Cond.get());
    visit(C->Then.get());
    visit(C->Else.get());
    return;
  }
  case VExpr::Forall:
  case VExpr::Exists: {
    const auto *Q = static_cast<const VQuantifiedExpr *>(E);
    visit(Q->Lo.get());
    visit(Q->Hi.get());
    Enclosing.push_back(Q);
    visit(Q->Body.get());
    Enclosing.pop_back();
    return;
  }
  case VExpr::HeapStore: {
    const auto *H = static_cast<const VHeapStoreExpr *>(E);
    visit(H->Ptr.get());
    visit(H->Val.get());
    return;
  }
  case VExpr::HeapFrame:
    for (const auto &[Lo, Hi] : static_cast<const VHeapFrameExpr *>(E)->Regions) {
      visit(Lo.get());
      visit(Hi.get());
    }
    return;
  case VExpr::FieldAccess:
    visit(static_cast<const VFieldAccessExpr *>(E)->Base.get());
    return;
  case VExpr::OverflowCheck: {
    const auto *O = static_cast<const VOverflowCheckExpr *>(E);
    visit(O->Lhs.get());
    visit(O->Rhs.get());
    return;
  }
  case VExpr::SpecCall: {
    const auto *C = static_cast<const VSpecCallExpr *>(E);
    for (const auto &Arg : C->Args)
      visit(Arg.get());
    auto It = FnMap.find(C->CalleeIdentity);
    if (It == FnMap.end() || !It->second || !Wanted(*C, *It->second))
      return;
    std::string Key;
    for (const VQuantifiedExpr *Q : Enclosing) {
      Key += "forall " + Q->Binder;
      if (!Q->Lo)
        Key += " unbounded";
      else if (!expressionKey(Q->Lo.get(), Key) ||
               !expressionKey(Q->Hi.get(), Key))
        return;
    }
    // Applications in different memory states are different values.
    Key += C->CalleeIdentity + '@' + C->HeapVar;
    for (const auto &Arg : C->Args)
      if (!expressionKey(Arg.get(), Key))
        return;
    Out.emplace(std::move(Key), FramedApplication{C, Enclosing});
    return;
  }
  case VExpr::Literal:
  case VExpr::Var:
  case VExpr::Result:
    return;
  }
}

/// A store outside the reads ranges of a spec leaves its value unchanged. For
/// each application, relate it across every store back from its heap state.
static void addFrameInstances(PassiveProgram &P, const FunctionMap &FnMap) {
  auto Framed = [](const VSpecCallExpr &Call, const VFunction &Spec) {
    return Call.ReadsHeap && !Call.HeapVar.empty() && !Spec.Reads.empty();
  };
  std::map<std::string, FramedApplication> Applications;
  std::vector<const VQuantifiedExpr *> Enclosing;
  for (const auto &S : P.Stmts)
    collectFramedApplications(S->Cond.get(), FnMap, Enclosing, Applications,
                              Framed);
  for (const auto &Exit : P.ExitAsserts)
    collectFramedApplications(Exit.Cond.get(), FnMap, Enclosing, Applications,
                              Framed);
  if (Applications.empty())
    return;

  // A step from one heap version to the next: a store at one address, or a
  // frame that keeps every cell outside some byte ranges.
  struct Store {
    size_t Index;
    const VExpr *Unless;
    std::string Before;
    std::string After;
    const VExpr *Address = nullptr;
    std::vector<std::pair<const VExpr *, const VExpr *>> Regions;
    SourceLocation Loc;
  };
  auto frameStep = [](const VExpr *Cond, Store &Step) {
    if (Cond->K != VExpr::HeapFrame)
      return false;
    const auto *Frame = static_cast<const VHeapFrameExpr *>(Cond);
    Step.Before = Frame->HeapBefore;
    Step.After = Frame->HeapAfter;
    Step.Loc = Frame->Loc;
    for (const auto &[Lo, Hi] : Frame->Regions)
      Step.Regions.push_back({Lo.get(), Hi.get()});
    return true;
  };
  std::map<std::string, Store> StoreInto;
  std::map<std::string, std::vector<std::string>> SameAs;
  for (size_t I = 0; I != P.Stmts.size(); ++I) {
    const PassiveStmt &S = *P.Stmts[I];
    if (S.K != PassiveStmt::Assume || !S.Cond)
      continue;
    const VExpr *Cond = S.Cond.get();
    const VExpr *Unless = nullptr;
    if (Cond->K == VExpr::BinOp &&
        static_cast<const VBinOpExpr *>(Cond)->Op == VBinOp::Or) {
      Unless = static_cast<const VBinOpExpr *>(Cond)->Lhs.get();
      Cond = static_cast<const VBinOpExpr *>(Cond)->Rhs.get();
    }
    if (Cond->K == VExpr::HeapStore) {
      const auto *H = static_cast<const VHeapStoreExpr *>(Cond);
      StoreInto.emplace(H->HeapAfter, Store{I, Unless, H->HeapBefore,
                                            H->HeapAfter, H->Ptr.get(), {},
                                            H->Loc});
      continue;
    }
    Store Frame{I, Unless, "", "", nullptr, {}, SourceLocation()};
    if (frameStep(Cond, Frame)) {
      StoreInto.emplace(Frame.After, std::move(Frame));
      continue;
    }
    if (Cond->K != VExpr::BinOp ||
        static_cast<const VBinOpExpr *>(Cond)->Op != VBinOp::Eq)
      continue;
    const auto *Eq = static_cast<const VBinOpExpr *>(Cond);
    if (Eq->Lhs->K != VExpr::Var)
      continue;
    const std::string &Name =
        static_cast<const VVarExpr *>(Eq->Lhs.get())->Name;
    auto addSource = [&](const VExpr *Source) {
      if (Source && Source->K == VExpr::Var)
        SameAs[Name].push_back(static_cast<const VVarExpr *>(Source)->Name);
    };
    if (Eq->Rhs->K == VExpr::Conditional) {
      const auto *C = static_cast<const VConditionalExpr *>(Eq->Rhs.get());
      addSource(C->Then.get());
      addSource(C->Else.get());
    } else {
      addSource(Eq->Rhs.get());
    }
  }
  if (StoreInto.empty())
    return;

  std::map<size_t, std::vector<std::unique_ptr<PassiveStmt>>> After;
  for (const auto &[Key, Application] : Applications) {
    const VSpecCallExpr *Call = Application.Call;
    const VFunction &Spec = *FnMap.at(Call->CalleeIdentity);
    std::set<std::string> Visited;
    std::vector<std::string> Work{Call->HeapVar};
    while (!Work.empty()) {
      std::string Heap = std::move(Work.back());
      Work.pop_back();
      if (!Visited.insert(Heap).second)
        continue;
      if (auto It = SameAs.find(Heap); It != SameAs.end())
        Work.insert(Work.end(), It->second.begin(), It->second.end());
      auto It = StoreInto.find(Heap);
      if (It == StoreInto.end())
        continue;
      const Store &S = It->second;
      const SourceLocation Loc = S.Loc;
      std::unique_ptr<VExpr> Outside;
      if (S.Address) {
        Outside = addressOutsideReads(Spec, Call->Args, S.Address, Loc);
      } else {
        Outside = makeBoolLiteral(true, Loc);
        for (const auto &[Lo, Hi] : S.Regions) {
          auto Disjoint = regionOutsideReads(Spec, Call->Args, Lo, Hi, Loc);
          if (!Disjoint) {
            Outside = nullptr;
            break;
          }
          Outside = makeAnd(std::move(Outside), std::move(Disjoint), Loc);
        }
      }
      if (!Outside)
        break;
      auto Later = cloneVExpr(Call);
      static_cast<VSpecCallExpr &>(*Later).HeapVar = S.After;
      auto Earlier = cloneVExpr(Call);
      static_cast<VSpecCallExpr &>(*Earlier).HeapVar = S.Before;
      std::unique_ptr<VExpr> Fact =
          makeImplies(std::move(Outside),
                      makeEq(std::move(Later), std::move(Earlier), Loc), Loc);
      // It holds at every binder value, whatever the range.
      for (auto Q = Application.Enclosing.rbegin();
           Q != Application.Enclosing.rend(); ++Q)
        Fact = std::make_unique<VForallExpr>(
            (*Q)->Binder, cloneVExpr((*Q)->Lo.get()),
            cloneVExpr((*Q)->Hi.get()), std::move(Fact), Loc, (*Q)->BinderType);
      if (S.Unless)
        Fact = std::make_unique<VBinOpExpr>(VBinOp::Or, cloneVExpr(S.Unless),
                                            std::move(Fact), VType::makeBool(),
                                            Loc);
      auto Instance = std::make_unique<PassiveStmt>();
      Instance->K = PassiveStmt::Assume;
      Instance->TraceEventCount = P.Stmts[S.Index]->TraceEventCount;
      Instance->Cond = std::move(Fact);
      After[S.Index].push_back(std::move(Instance));
      Work.push_back(S.Before);
    }
  }
  if (After.empty())
    return;
  std::vector<std::unique_ptr<PassiveStmt>> Stmts;
  for (size_t I = 0; I != P.Stmts.size(); ++I) {
    Stmts.push_back(std::move(P.Stmts[I]));
    if (auto It = After.find(I); It != After.end())
      for (auto &Instance : It->second)
        Stmts.push_back(std::move(Instance));
  }
  P.Stmts = std::move(Stmts);
}

/// A spec's proved postcondition, and an inductive predicate's unfolding,
/// hold at every application of it.
static void addSpecPostInstances(PassiveProgram &P, const FunctionMap &FnMap,
                                 const std::set<std::string> &Withheld) {
  auto WithPost = [&](const VSpecCallExpr &, const VFunction &Spec) {
    return (!Spec.Postconditions.empty() || Spec.Unfolding) &&
           !Withheld.count(Spec.Identity);
  };
  std::map<std::string, FramedApplication> Applications;
  std::vector<const VQuantifiedExpr *> Enclosing;
  for (const auto &Assumption : P.EntryAssumes)
    collectFramedApplications(Assumption.get(), FnMap, Enclosing, Applications,
                              WithPost);
  for (const auto &S : P.Stmts)
    collectFramedApplications(S->Cond.get(), FnMap, Enclosing, Applications,
                              WithPost);
  for (const auto &Exit : P.ExitAsserts)
    collectFramedApplications(Exit.Cond.get(), FnMap, Enclosing, Applications,
                              WithPost);
  std::vector<std::unique_ptr<PassiveStmt>> Facts;
  for (const auto &[Key, Application] : Applications) {
    const VSpecCallExpr &Call = *Application.Call;
    const VFunction &Spec = *FnMap.at(Call.CalleeIdentity);
    std::unique_ptr<VExpr> Fact =
        specApplicationFacts(Spec, Call.Args, &Call, Call.Loc,
                             Call.ReadsHeap ? Call.HeapVar : std::string());
    if (!Fact)
      continue;
    if (!Spec.Postconditions.empty())
      P.AssumedPosts.insert(Spec.Identity);
    if (Spec.Unfolding)
      P.AssumedUnfoldings.insert(Spec.Identity);
    for (auto Q = Application.Enclosing.rbegin();
         Q != Application.Enclosing.rend(); ++Q)
      Fact = std::make_unique<VForallExpr>(
          (*Q)->Binder, cloneVExpr((*Q)->Lo.get()), cloneVExpr((*Q)->Hi.get()),
          std::move(Fact), Call.Loc, (*Q)->BinderType);
    auto Instance = std::make_unique<PassiveStmt>();
    Instance->K = PassiveStmt::Assume;
    Instance->Cond = std::move(Fact);
    Facts.push_back(std::move(Instance));
  }
  P.Stmts.insert(P.Stmts.begin(), std::make_move_iterator(Facts.begin()),
                 std::make_move_iterator(Facts.end()));
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
  /// Loops being passivized, innermost last.
  struct LoopFrame {
    const VWhileStmt *Loop = nullptr;
    const std::vector<std::unique_ptr<VExpr>> *OldDecreases = nullptr;
    std::vector<std::unique_ptr<VExpr>> BreakGuards;
    /// The heap before the loop, which its declared modifies frame.
    std::string EntryHeap;
  };
  std::vector<LoopFrame> LoopFrames;
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
  /// Names the body assigns: a parameter outside it keeps its entry value.
  std::set<std::string> AssignedNames;

  /// A byte range [Lo, Hi) of passive addresses.
  struct Region {
    std::unique_ptr<VExpr> Lo;
    std::unique_ptr<VExpr> Hi;
    /// Set when the region is the one heap cell at Lo (Hi is Lo + 1), which
    /// holds a value of this type.
    std::optional<VType> Cell;
  };

  static Region cellRegion(const VExpr *Address, const VType &Ty,
                           SourceLocation Loc) {
    return Region{cloneVExpr(Address),
                  addBytes(cloneVExpr(Address),
                           std::make_unique<VLiteralExpr>(
                               1, pointerOffsetType(), Loc),
                           Loc),
                  Ty};
  }

  static std::unique_ptr<VExpr> addBytes(std::unique_ptr<VExpr> Pointer,
                                         std::unique_ptr<VExpr> Bytes,
                                         SourceLocation Loc) {
    return std::make_unique<VBinOpExpr>(VBinOp::Add, std::move(Pointer),
                                        std::move(Bytes), VType::makePtr(),
                                        Loc);
  }

  /// The cells [Address, Address + Count * ElementSize).
  static Region rangeBytes(const VExpr *Address, const VExpr *Count,
                           uint64_t ElementSize, SourceLocation Loc) {
    VType MathTy = Count->Ty;
    MathTy.IntMode = VIntMode::Math;
    auto Bytes = std::make_unique<VBinOpExpr>(
        VBinOp::Mul,
        std::make_unique<VCastExpr>(cloneVExpr(Count), Count->Ty, MathTy, Loc),
        std::make_unique<VLiteralExpr>(std::to_string(ElementSize), MathTy,
                                       Loc),
        MathTy, Loc);
    return Region{cloneVExpr(Address),
                  addBytes(cloneVExpr(Address), std::move(Bytes), Loc)};
  }

  static uint64_t cellBytes(const VType &Ty) {
    return std::max<uint64_t>(Ty.isInt() ? Ty.BitWidth / 8 : 8, 1);
  }

  /// Whether the inner footprint lies within the outer one. The heap holds
  /// one cell per address: a cell footprint is its address, a range its
  /// addresses, and a region the object its pointer addresses (a region
  /// footprint contains footprints rooted at the same pointer). InnerBytes,
  /// when known, bounds an inner range or region.
  static std::unique_ptr<VExpr>
  footprintWithin(const VExpr *OuterPtr, bool OuterIsRegion,
                  const std::optional<Region> &OuterBytes,
                  const VExpr *InnerPtr, bool InnerIsRegion, bool InnerIsRange,
                  const std::optional<Region> &InnerBytes, SourceLocation Loc) {
    if (OuterIsRegion)
      return samePointerRegion(OuterPtr, InnerPtr, Loc);
    auto Empty = [&](const Region &R) {
      return std::make_unique<VBinOpExpr>(VBinOp::Le, cloneVExpr(R.Hi.get()),
                                          cloneVExpr(R.Lo.get()),
                                          VType::makeBool(), Loc);
    };
    auto Le = [&](const VExpr *L, const VExpr *R) {
      return std::make_unique<VBinOpExpr>(VBinOp::Le, cloneVExpr(L),
                                          cloneVExpr(R), VType::makeBool(),
                                          Loc);
    };
    if (!OuterBytes) {
      if (!InnerIsRegion && !InnerIsRange)
        return makeEq(cloneVExpr(OuterPtr), cloneVExpr(InnerPtr), Loc);
      if (InnerIsRange && InnerBytes)
        return Empty(*InnerBytes);
      return makeBoolLiteral(false, Loc);
    }
    if (!InnerIsRegion && !InnerIsRange)
      return makeAnd(Le(OuterBytes->Lo.get(), InnerPtr),
                     std::make_unique<VBinOpExpr>(
                         VBinOp::Lt, cloneVExpr(InnerPtr),
                         cloneVExpr(OuterBytes->Hi.get()), VType::makeBool(),
                         Loc),
                     Loc);
    if (!InnerBytes)
      return makeBoolLiteral(false, Loc);
    return makeOr(Empty(*InnerBytes),
                  makeAnd(Le(OuterBytes->Lo.get(), InnerBytes->Lo.get()),
                          Le(InnerBytes->Hi.get(), OuterBytes->Hi.get()), Loc),
                  Loc);
  }

  /// The object a parameter addresses at entry, in passive terms, when the
  /// parameter still holds its entry value.
  std::optional<Region>
  parameterRegion(const std::string &Name,
                  const std::map<std::string, std::string> &Renames,
                  SourceLocation Loc) {
    if (AssignedNames.count(Name))
      return std::nullopt;
    return entryObjectRegion(Name, Renames, Loc);
  }

  /// The regions of the objects a pointer rooted at Root may address, when
  /// its origins are known: parameters' entry objects and globals.
  bool originRegions(const VExpr *Root,
                     const std::map<std::string, std::string> &Renames,
                     SourceLocation Loc, std::vector<Region> &Out) {
    auto Origins = pointerOrigins(Root);
    if (!Root || Root->K != VExpr::Var || !Origins || Origins->empty())
      return false;
    std::vector<Region> Found;
    for (const std::string &Origin : *Origins) {
      if (isGlobalOrigin(Origin)) {
        auto [Address, Size] = globalOriginExtent(Origin);
        auto Start =
            std::make_unique<VLiteralExpr>(Address, VType::makePtr(), Loc);
        auto End = addBytes(cloneVExpr(Start.get()),
                            std::make_unique<VLiteralExpr>(
                                std::to_string(std::max<uint64_t>(Size, 1)),
                                pointerOffsetType(), Loc),
                            Loc);
        Found.push_back(Region{std::move(Start), std::move(End)});
        continue;
      }
      auto Object = entryObjectRegion(Origin, Renames, Loc);
      if (!Object)
        return false;
      Found.push_back(std::move(*Object));
    }
    for (Region &R : Found)
      Out.push_back(std::move(R));
    return true;
  }

  /// The object a parameter addressed at entry.
  std::optional<Region>
  entryObjectRegion(const std::string &Name,
                    const std::map<std::string, std::string> &Renames,
                    SourceLocation Loc) {
    for (const AbstractObject &Object : abstractObjects(Fn)) {
      if (Object.Name != Name)
        continue;
      CloneCtx EntryCtx{Renames, OldState, true};
      VVarExpr Parameter(Name, Object.PointerType, Loc);
      auto Lo = cloneExpr(&Parameter, EntryCtx);
      const uint64_t Stride = Object.PointerType.PointeeSizeBytes;
      std::unique_ptr<VExpr> Bytes;
      if (Object.Length) {
        auto Length = cloneExpr(Object.Length, EntryCtx);
        VType MathTy = Length->Ty;
        MathTy.IntMode = VIntMode::Math;
        Bytes = std::make_unique<VBinOpExpr>(
            VBinOp::Mul,
            std::make_unique<VCastExpr>(std::move(Length), Object.Length->Ty,
                                        MathTy, Loc),
            std::make_unique<VLiteralExpr>(std::to_string(Stride), MathTy, Loc),
            MathTy, Loc);
      } else {
        Bytes = std::make_unique<VLiteralExpr>(std::to_string(Stride),
                                               pointerOffsetType(), Loc);
      }
      auto Hi = addBytes(cloneVExpr(Lo.get()), std::move(Bytes), Loc);
      return Region{std::move(Lo), std::move(Hi)};
    }
    return std::nullopt;
  }

  /// The region a write rooted at Root may reach, or nullopt when it cannot
  /// be bounded: a parameter's object or a global's cell.
  std::optional<Region>
  rootRegion(const VExpr *Root, const std::map<std::string, std::string> &Renames,
             SourceLocation Loc) {
    if (!Root)
      return std::nullopt;
    if (isGlobalCell(Root)) {
      const uint64_t Size = std::max<uint64_t>(Root->Ty.PointeeSizeBytes, 1);
      return Region{cloneVExpr(Root),
                    addBytes(cloneVExpr(Root),
                             std::make_unique<VLiteralExpr>(
                                 std::to_string(Size), pointerOffsetType(),
                                 Loc),
                             Loc)};
    }
    if (Root->K == VExpr::Var &&
        static_cast<const VVarExpr *>(Root)->ProvenanceVariable.empty())
      return parameterRegion(static_cast<const VVarExpr *>(Root)->Name,
                             Renames, Loc);
    return std::nullopt;
  }

  /// A loop's declared footprints as byte ranges in the state Ctx reads, or
  /// nullopt when a region footprint's object is not known.
  std::optional<std::vector<Region>>
  loopFootprintRegions(const VWhileStmt &W, const CloneCtx &Ctx,
                       const std::map<std::string, std::string> &Renames) {
    std::vector<Region> Out;
    for (const VFootprint &F : W.Modifies) {
      const auto *Load = static_cast<const VLoadExpr *>(F.Target.get());
      if (isRegionFootprint(F, Fn.ReferenceParams)) {
        auto R = rootRegion(addressRoot(Load->Ptr.get()), Renames, Load->Loc);
        if (!R)
          return std::nullopt;
        Out.push_back(std::move(*R));
        continue;
      }
      auto Address = cloneExpr(Load->Ptr.get(), Ctx);
      if (F.Count) {
        auto Count = cloneExpr(F.Count.get(), Ctx);
        Out.push_back(rangeBytes(Address.get(), Count.get(), F.ElementSize,
                                 Load->Loc));
        continue;
      }
      auto End = addBytes(cloneVExpr(Address.get()),
                          std::make_unique<VLiteralExpr>(
                              std::to_string(cellBytes(Load->Ty)),
                              pointerOffsetType(), Load->Loc),
                          Load->Loc);
      Out.push_back(Region{std::move(Address), std::move(End)});
    }
    return Out;
  }

  /// Check a loop's declared modifies where an iteration ends: every cell
  /// outside them, read in this state, still holds its value before the loop.
  void emitLoopFrameCheck(PassiveProgram &P, const VWhileStmt &W,
                          const std::string &EntryHeap,
                          const std::map<std::string, std::string> &Renames,
                          const VExpr *Active) {
    if (W.Modifies.empty() || EntryHeap.empty())
      return;
    const SourceLocation Loc = W.Modifies.front().Target->Loc;
    CloneCtx Ctx{Renames, OldState, false};
    for (const VFootprint &F : W.Modifies) {
      const VExpr *Pointer =
          static_cast<const VLoadExpr *>(F.Target.get())->Ptr.get();
      auto Address = cloneExpr(Pointer, Ctx);
      emitExprSafety(P, Address.get(), Active, Loc, Renames, false, Pointer);
      if (F.Count) {
        auto Count = cloneExpr(F.Count.get(), Ctx);
        emitExprSafety(P, Count.get(), Active, Loc, Renames, false,
                       F.Count.get());
      }
    }
    auto Regions = loopFootprintRegions(W, Ctx, Renames);
    if (!Regions) {
      emitPassive(P, PassiveStmt::Assert, makeBoolLiteral(false, Loc), Active,
                  Loc, ProofObligationKind::Unsupported,
                  "a loop modifies footprint names a whole object through a "
                  "pointer whose object is not known");
      return;
    }
    auto Current = Renames.find(VHeapName);
    if (Current == Renames.end())
      return;
    emitPassive(P, PassiveStmt::Assert,
                heapFrame(EntryHeap, Current->second, *Regions, Loc), Active,
                Loc, ProofObligationKind::Frame);
  }

  /// The one cell a write at Address reaches when Address is a parameter
  /// itself: its entry value.
  std::optional<Region>
  parameterCell(const VExpr *Address, const VType &CellType,
                const std::map<std::string, std::string> &Renames,
                SourceLocation Loc) {
    while (Address && Address->K == VExpr::Cast)
      Address = static_cast<const VCastExpr *>(Address)->Inner.get();
    if (!Address || Address->K != VExpr::Var ||
        !static_cast<const VVarExpr *>(Address)->ProvenanceVariable.empty())
      return std::nullopt;
    auto Object = parameterRegion(static_cast<const VVarExpr *>(Address)->Name,
                                  Renames, Loc);
    if (!Object)
      return std::nullopt;
    return cellRegion(Object->Lo.get(), CellType, Loc);
  }

  /// The regions a loop body may write, or false when a write cannot be
  /// bounded and the whole heap must be forgotten.
  /// The regions of the function's own modifies, in the entry state, when
  /// they bound every write: no represented or dynamic storage, which the
  /// frame check also admits.
  bool functionFrameRegions(const std::map<std::string, std::string> &Renames,
                            SourceLocation Loc, std::vector<Region> &Out) {
    if (Fn.Modifies.empty() || Fn.UsesDynamicStorage ||
        !OwnedAllocationIdentities.empty())
      return false;
    CloneCtx EntryCtx{Renames, OldState, true};
    for (const VFootprint &M : Fn.Modifies) {
      if (!M.Target || M.Target->K != VExpr::Load)
        return false;
      const auto *Load = static_cast<const VLoadExpr *>(M.Target.get());
      auto Ptr = cloneExpr(Load->Ptr.get(), EntryCtx);
      if (M.Count) {
        auto Count = cloneExpr(M.Count.get(), EntryCtx);
        Out.push_back(rangeBytes(Ptr.get(), Count.get(), M.ElementSize, Loc));
        continue;
      }
      if (isRegionFootprint(M, Fn.ReferenceParams)) {
        auto R = rootRegion(addressRoot(Load->Ptr.get()), Renames, Loc);
        if (!R)
          return false;
        Out.push_back(std::move(*R));
        continue;
      }
      Out.push_back(cellRegion(Ptr.get(), Load->Ty, Loc));
    }
    return true;
  }

  bool loopWriteRegions(const std::vector<std::unique_ptr<VStmt>> &Stmts,
                        const std::map<std::string, std::string> &Renames,
                        std::vector<Region> &Out) {
    for (const auto &S : Stmts) {
      switch (S->K) {
      case VStmt::Store: {
        const auto &St = static_cast<const VStoreStmt &>(*S);
        auto R = parameterCell(St.Ptr.get(), St.Value->Ty, Renames, St.Loc);
        if (!R &&
            originRegions(addressRoot(St.Ptr.get()), Renames, St.Loc, Out))
          break;
        if (!R)
          R = rootRegion(addressRoot(St.Ptr.get()), Renames, St.Loc);
        if (!R)
          return false;
        Out.push_back(std::move(*R));
        break;
      }
      case VStmt::Call: {
        const auto &C = static_cast<const VCallStmt &>(*S);
        auto It = FnMap.find(C.CalleeIdentity);
        if (It == FnMap.end())
          return false;
        const VFunction *Callee = It->second;
        if (Callee->IsSpec || Callee->IsProof)
          break;
        if (Callee->UsesDynamicStorage || hasImplicitHeapEffect(*Callee, FnMap))
          return false;
        for (const VFootprint &M : Callee->Modifies) {
          if (!M.Target || M.Target->K != VExpr::Load)
            return false;
          const VExpr *CalleeRoot = addressRoot(
              static_cast<const VLoadExpr *>(M.Target.get())->Ptr.get());
          if (CalleeRoot && isGlobalCell(CalleeRoot)) {
            auto R = rootRegion(CalleeRoot, Renames, C.Loc);
            Out.push_back(std::move(*R));
            continue;
          }
          if (!CalleeRoot || CalleeRoot->K != VExpr::Var)
            return false;
          const std::string &Param =
              static_cast<const VVarExpr *>(CalleeRoot)->Name;
          const VExpr *Actual = nullptr;
          for (unsigned I = 0;
               I < Callee->Params.size() && I < C.Args.size(); ++I)
            if (Callee->Params[I].first == Param)
              Actual = C.Args[I].get();
          // A footprint that is the one cell its parameter addresses: an
          // exact cell there, or a single scalar object.
          const auto *Target = static_cast<const VLoadExpr *>(M.Target.get());
          const VExpr *TargetPtr = Target->Ptr.get();
          while (TargetPtr->K == VExpr::Cast)
            TargetPtr = static_cast<const VCastExpr *>(TargetPtr)->Inner.get();
          const bool OneCell =
              !M.Count && TargetPtr == CalleeRoot &&
              (!isRegionFootprint(M, Callee->ReferenceParams) ||
               (Callee->ObjectModel &&
                (Target->Ty.isInt() || Target->Ty.Kind == VTypeKind::Bool ||
                 Target->Ty.Kind == VTypeKind::Ptr) &&
                llvm::none_of(Callee->ValidExtents,
                              [&](const VValidExtent &Extent) {
                                return Extent.Base == Param;
                              })));
          if (OneCell)
            if (auto Cell = parameterCell(Actual, Target->Ty, Renames, C.Loc)) {
              Out.push_back(std::move(*Cell));
              continue;
            }
          if (originRegions(addressRoot(Actual), Renames, C.Loc, Out))
            continue;
          auto R = rootRegion(addressRoot(Actual), Renames, C.Loc);
          if (!R)
            return false;
          Out.push_back(std::move(*R));
        }
        break;
      }
      case VStmt::Allocate:
      case VStmt::Free:
        return false;
      case VStmt::If: {
        const auto &I = static_cast<const VIfStmt &>(*S);
        if (!loopWriteRegions(I.Then, Renames, Out) ||
            !loopWriteRegions(I.Else, Renames, Out))
          return false;
        break;
      }
      case VStmt::While:
        if (!loopWriteRegions(static_cast<const VWhileStmt &>(*S).Body,
                              Renames, Out))
          return false;
        break;
      case VStmt::Seq:
        if (!loopWriteRegions(static_cast<const VSeqStmt &>(*S).Stmts,
                              Renames, Out))
          return false;
        break;
      default:
        break;
      }
    }
    return true;
  }

  /// The element offset c of a slice actual `base + S*c` that a quantifier
  /// indexes as `(base + S*c) + S*j`.
  static const VExpr *sliceOffset(const VExpr *E, const std::string &Binder) {
    if (!E)
      return nullptr;
    auto scaled = [](const VExpr *Term, uint64_t &Stride) -> const VExpr * {
      if (Term->K == VExpr::BinOp) {
        const auto *M = static_cast<const VBinOpExpr *>(Term);
        if (M->Op == VBinOp::Mul && M->Rhs->K == VExpr::Literal) {
          Stride = std::stoull(static_cast<const VLiteralExpr *>(M->Rhs.get())
                                   ->Value);
          return M->Lhs.get();
        }
      }
      Stride = 1;
      return Term;
    };
    if (E->K == VExpr::Load) {
      const VExpr *Address = static_cast<const VLoadExpr *>(E)->Ptr.get();
      if (Address->K == VExpr::BinOp) {
        const auto *Outer = static_cast<const VBinOpExpr *>(Address);
        if (Outer->Op == VBinOp::Add && Outer->Lhs->Ty.Kind == VTypeKind::Ptr &&
            Outer->Lhs->K == VExpr::BinOp) {
          const auto *Inner = static_cast<const VBinOpExpr *>(Outer->Lhs.get());
          uint64_t IndexStride = 0, OffsetStride = 0;
          const VExpr *Index = scaled(Outer->Rhs.get(), IndexStride);
          if (Inner->Op == VBinOp::Add &&
              Inner->Lhs->Ty.Kind == VTypeKind::Ptr && Index->K == VExpr::Var &&
              static_cast<const VVarExpr *>(Index)->Name == Binder) {
            const VExpr *Offset = scaled(Inner->Rhs.get(), OffsetStride);
            if (OffsetStride == IndexStride && Offset->Ty.isInt())
              return Offset;
          }
        }
      }
    }
    const VExpr *Found = nullptr;
    auto visit = [&](const VExpr *Child) {
      if (!Found)
        Found = sliceOffset(Child, Binder);
    };
    switch (E->K) {
    case VExpr::BinOp:
      visit(static_cast<const VBinOpExpr *>(E)->Lhs.get());
      visit(static_cast<const VBinOpExpr *>(E)->Rhs.get());
      break;
    case VExpr::UnaryOp:
      visit(static_cast<const VUnaryOpExpr *>(E)->Operand.get());
      break;
    case VExpr::Cast:
      visit(static_cast<const VCastExpr *>(E)->Inner.get());
      break;
    case VExpr::Conditional:
      visit(static_cast<const VConditionalExpr *>(E)->Cond.get());
      visit(static_cast<const VConditionalExpr *>(E)->Then.get());
      visit(static_cast<const VConditionalExpr *>(E)->Else.get());
      break;
    case VExpr::Load:
      visit(static_cast<const VLoadExpr *>(E)->Ptr.get());
      break;
    case VExpr::Old:
      visit(static_cast<const VOldExpr *>(E)->Inner.get());
      break;
    default:
      break;
    }
    return Found;
  }

  /// A contract quantifier that indexes a slice actual `base + c` from zero
  /// is restated over base's indices: j := k - c is a change of variables,
  /// and it lets the caller's own terms trigger the instantiation.
  std::unique_ptr<VExpr> rebaseSliceBinders(std::unique_ptr<VExpr> E) {
    if (!E)
      return E;
    switch (E->K) {
    case VExpr::BinOp: {
      auto *B = static_cast<VBinOpExpr *>(E.get());
      B->Lhs = rebaseSliceBinders(std::move(B->Lhs));
      B->Rhs = rebaseSliceBinders(std::move(B->Rhs));
      return E;
    }
    case VExpr::UnaryOp: {
      auto *U = static_cast<VUnaryOpExpr *>(E.get());
      U->Operand = rebaseSliceBinders(std::move(U->Operand));
      return E;
    }
    case VExpr::Forall:
    case VExpr::Exists: {
      auto *Q = static_cast<VQuantifiedExpr *>(E.get());
      Q->Body = rebaseSliceBinders(std::move(Q->Body));
      if (Q->BinderType.IntMode != VIntMode::Math)
        return E;
      const VExpr *Offset = sliceOffset(Q->Body.get(), Q->Binder);
      if (!Offset)
        return E;
      const SourceLocation Loc = Q->Loc;
      const VType MathTy = Q->BinderType;
      auto mathOf = [&](const VExpr *V) -> std::unique_ptr<VExpr> {
        if (V->Ty.IntMode == VIntMode::Math)
          return cloneVExpr(V);
        VType To = V->Ty;
        To.IntMode = VIntMode::Math;
        return std::make_unique<VCastExpr>(cloneVExpr(V), V->Ty, To, Loc);
      };
      const std::string Rebased = Q->Binder + "_rebased";
      std::map<std::string, std::unique_ptr<VExpr>> Shift;
      Shift[Q->Binder] = std::make_unique<VBinOpExpr>(
          VBinOp::Sub, std::make_unique<VVarExpr>(Rebased, MathTy, Loc),
          mathOf(Offset), MathTy, Loc);
      auto Body = substParamsInExpr(Q->Body.get(), Shift);
      // Over all integers the shift changes no range.
      std::unique_ptr<VExpr> Lo, Hi;
      if (Q->Lo) {
        Lo = std::make_unique<VBinOpExpr>(VBinOp::Add, mathOf(Q->Lo.get()),
                                          mathOf(Offset), MathTy, Loc);
        Hi = std::make_unique<VBinOpExpr>(VBinOp::Add, mathOf(Q->Hi.get()),
                                          mathOf(Offset), MathTy, Loc);
      }
      if (!Body)
        return E;
      if (E->K == VExpr::Forall)
        return std::make_unique<VForallExpr>(Rebased, std::move(Lo),
                                             std::move(Hi), std::move(Body),
                                             Loc, MathTy);
      return std::make_unique<VExistsExpr>(Rebased, std::move(Lo),
                                           std::move(Hi), std::move(Body), Loc,
                                           MathTy);
    }
    default:
      return E;
    }
  }

  /// After equals Before outside the regions, cell by cell.
  std::unique_ptr<VExpr> heapFrame(const std::string &Before,
                                   const std::string &After,
                                   const std::vector<Region> &Regions,
                                   SourceLocation Loc) {
    std::vector<std::pair<std::unique_ptr<VExpr>, std::unique_ptr<VExpr>>>
        Bounds;
    for (const Region &R : Regions)
      Bounds.emplace_back(cloneVExpr(R.Lo.get()), cloneVExpr(R.Hi.get()));
    return std::make_unique<VHeapFrameExpr>(Before, After, std::move(Bounds),
                                            Loc);
  }

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
      case VTypeKind::Seq:
      case VTypeKind::Set:
      case VTypeKind::Multiset:
      case VTypeKind::Map:
        break;
      }
    }
    TraceEvents.push_back(std::move(Event));
  }

  void
  emitPassive(PassiveProgram &P, PassiveStmt::Kind K,
              std::unique_ptr<VExpr> Cond, const VExpr *Guard = nullptr,
              SourceLocation Loc = SourceLocation(),
              ProofObligationKind ProofKind = ProofObligationKind::Unsupported,
              std::string Note = "") {
    // A generated proof about specs evaluates them as specs do: totally.
    if (Fn.TotalExpressions && K == PassiveStmt::Assert &&
        isDefinedness(ProofKind))
      return;
    auto PS = std::make_unique<PassiveStmt>();
    PS->K = K;
    PS->ProofKind = ProofKind;
    PS->Note = std::move(Note);
    PS->TraceEventCount = TraceEvents.size();
    if (Guard)
      Cond = makeImplies(cloneVExpr(Guard), std::move(Cond), Loc);
    PS->Cond = std::move(Cond);
    P.Stmts.push_back(std::move(PS));
  }

  static bool isDefinedness(ProofObligationKind Kind) {
    switch (Kind) {
    case ProofObligationKind::Overflow:
    case ProofObligationKind::DivisionByZero:
    case ProofObligationKind::Shift:
    case ProofObligationKind::Bounds:
    case ProofObligationKind::Dereference:
    case ProofObligationKind::Initialization:
    case ProofObligationKind::PointerDifference:
    case ProofObligationKind::PointerValidity:
      return true;
    default:
      return false;
    }
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
    emitPassive(P, PassiveStmt::Assert, std::move(Coverage), nullptr,
                SourceLocation(), ProofObligationKind::MissingReturn);

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
    case VStmt::Break:
    case VStmt::Continue:
      break;
    case VStmt::Havoc:
      Out.insert(static_cast<const VHavocStmt &>(S).Target);
      break;
    }
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
    SafetyChecks Checks;
    collectSafety(
        SafetySource ? SafetySource : E, &FnMap,
        SafetySource ? &Fn.ValidExtents : &ActiveValidExtents,
        SafetySource ? &SourcePointerParameterNames : &PointerParameterNames,
        Checks, Fn.ObjectModel, SafetySource ? &Fn.ValidExtents : nullptr);
    groupByKind(Checks);
    CloneCtx Ctx{Renames, OldState, false};
    for (const SafetyCheck &Check : Checks)
      emitPassive(P, PassiveStmt::Assert, cloneExpr(Check.Cond.get(), Ctx),
                  Guard, Loc, Check.Kind, Check.Note);
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
    emitPassive(P, PassiveStmt::Assume,
                makeOr(cloneVExpr(IsNull.get()),
                       belowGlobals(Pointer.get(), Summary.SizeBytes, Loc),
                       Loc));

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
    AssignedNames = assignedNames(Fn.Body);
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
    for (const auto &[Name, Assumes] : Fn.Behaviors) {
      CloneCtx PCtx{Renames, OldState, false};
      P.BehaviorAssumes.emplace_back(Name, cloneExpr(Assumes.get(), PCtx));
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
    if (Fn.ObjectModel) {
      CloneCtx PCtx{Renames, OldState, false};
      for (const AbstractObject &Object : abstractObjects(Fn))
        P.EntryAssumes.push_back(cloneExpr(
            objectPlacement(Object, SourceLocation()).get(), PCtx));
    }

    std::unique_ptr<VExpr> Active = makeBoolLiteral(true, SourceLocation());
    for (const auto &S : Fn.Body)
      processStmt(*S, P, Renames, Active);
    finalizeReturns(P, Renames, Active.get());

    // A parameter in a postcondition is the caller's argument: its value at
    // entry, whatever the body assigned to its copy.
    std::map<std::string, std::string> PostRenames = Renames;
    for (const auto &[Name, Entry] : OldState) {
      if (Entry->K != VExpr::Var)
        continue;
      const bool OfParameter = llvm::any_of(Fn.Params, [&](const auto &P) {
        return Name == P.first ||
               llvm::StringRef(Name).starts_with(P.first + ".");
      });
      if (OfParameter)
        PostRenames[Name] = static_cast<const VVarExpr &>(*Entry).Name;
    }
    for (size_t I = 0; I != Fn.Postconditions.size(); ++I) {
      const VExpr *Post = Fn.Postconditions[I].get();
      CloneCtx PCtx{PostRenames, OldState, false};
      auto BoundPost = cloneExpr(Post, PCtx);
      // A returned pointer without provenance is valid as its membership in
      // the parameters' objects shows.
      if (Fn.ObjectModel && !Fn.UsesDynamicStorage &&
          postconditionKind(Fn, I) == ProofObligationKind::PointerValidity)
        BoundPost = abstractValidity(std::move(BoundPost), Renames);
      emitMathBridge(P, BoundPost.get(), nullptr, BoundPost->Loc);
      SafetyChecks Checks;
      collectSafety(Post, &FnMap, &Fn.ValidExtents,
                    &SourcePointerParameterNames, Checks, Fn.ObjectModel,
                    &Fn.ValidExtents);
      groupByKind(Checks);
      for (const SafetyCheck &Check : Checks) {
        if (Fn.TotalExpressions && isDefinedness(Check.Kind))
          continue;
        // Anchor at the clause; an unfolded helper's operators may lie in
        // another file.
        auto Cond = cloneExpr(Check.Cond.get(), PCtx);
        Cond->Loc = Post->Loc;
        Cond->EndLoc = Post->EndLoc;
        P.ExitAsserts.push_back({Check.Kind, std::move(Cond)});
      }
      P.ExitAsserts.push_back({postconditionKind(Fn, I), std::move(BoundPost)});
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
    addFrameInstances(P, FnMap);
    addSpecPostInstances(P, FnMap, Fn.FactsWithheld);
    return P;
  }

  /// In the object model a pointer without provenance is valid where it lies
  /// in one of the caller's objects or is a known valid object of its own,
  /// and abstract storage is initialized.
  std::unique_ptr<VExpr>
  abstractValidity(std::unique_ptr<VExpr> E,
                   const std::map<std::string, std::string> &Renames) {
    if (!E)
      return E;
    switch (E->K) {
    case VExpr::UnaryOp: {
      auto *U = static_cast<VUnaryOpExpr *>(E.get());
      if ((U->Op == VUnaryOp::ValidPtr || U->Op == VUnaryOp::InitializedPtr) &&
          !hasPointerProvenance(U->Operand.get())) {
        if (U->Op == VUnaryOp::InitializedPtr)
          return makeBoolLiteral(true, U->Loc);
        CloneCtx EntryCtx{Renames, OldState, true};
        const SourceLocation Loc = U->Loc;
        auto Member = objectMembership(
            abstractObjects(Fn), U->Operand.get(), /*Closed=*/false, Loc,
            [&](const VExpr *V) { return cloneExpr(V, EntryCtx); });
        return makeOr(std::move(Member), std::move(E), Loc);
      }
      U->Operand = abstractValidity(std::move(U->Operand), Renames);
      return E;
    }
    case VExpr::BinOp: {
      auto *B = static_cast<VBinOpExpr *>(E.get());
      B->Lhs = abstractValidity(std::move(B->Lhs), Renames);
      B->Rhs = abstractValidity(std::move(B->Rhs), Renames);
      return E;
    }
    case VExpr::Conditional: {
      auto *C = static_cast<VConditionalExpr *>(E.get());
      C->Cond = abstractValidity(std::move(C->Cond), Renames);
      C->Then = abstractValidity(std::move(C->Then), Renames);
      C->Else = abstractValidity(std::move(C->Else), Renames);
      return E;
    }
    default:
      return E;
    }
  }

  void emitCallStmt(const VCallStmt &C, PassiveProgram &P,
                    std::map<std::string, std::string> &Renames) {
    auto CalleeIt = FnMap.find(C.CalleeIdentity);
    if (CalleeIt == FnMap.end()) {
      emitPassive(P, PassiveStmt::Assert, makeBoolLiteral(false, C.Loc),
                  nullptr, C.Loc, ProofObligationKind::Unsupported,
                  "a call of " + C.Callee +
                      ", whose contract is not available");
      return;
    }
    const VFunction *Callee = CalleeIt->second;
    if (Callee->IsSpec)
      return;
    const bool ReturnsFreshOwned =
        Callee->FreshOwnedReturn && Callee->ReturnType.Kind == VTypeKind::Ptr &&
        !C.ResultTarget.empty() && !C.ResultProvenanceTarget.empty();
    if (Callee->UsesDynamicStorage && !ReturnsFreshOwned) {
      emitPassive(P, PassiveStmt::Assert, makeBoolLiteral(false, C.Loc),
                  nullptr, C.Loc, ProofObligationKind::Unsupported,
                  C.Callee + " allocates or frees storage, and only a fresh "
                             "allocation it returns is modeled at a call");
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
          emitPassive(P, PassiveStmt::Assert, makeBoolLiteral(false, C.Loc),
                      nullptr, C.Loc, ProofObligationKind::Unsupported,
                      "a pointer to local or dynamic storage is passed to " +
                          C.Callee +
                          ", which may keep, offset, or free it, or has no "
                          "verified body");
          return;
        }
      }
    if (!C.ResultProvenanceTarget.empty() && DynamicParams.empty() &&
        !ReturnsFreshOwned) {
      emitPassive(P, PassiveStmt::Assert, makeBoolLiteral(false, C.Loc),
                  nullptr, C.Loc, ProofObligationKind::Unsupported,
                  "the pointer " + C.Callee +
                      " returns is neither a fresh allocation nor one of its "
                      "dynamic-storage arguments");
      return;
    }
    if (Callee->ReturnType.Kind == VTypeKind::Ptr && !C.ResultTarget.empty() &&
        !ReturnsFreshOwned && !DynamicParams.empty() &&
        (C.ResultProvenanceTarget.empty() ||
         !pointerReturnsComeFrom(*Callee, DynamicParams))) {
      emitPassive(P, PassiveStmt::Assert, makeBoolLiteral(false, C.Loc),
                  nullptr, C.Loc, ProofObligationKind::Unsupported,
                  C.Callee + " may return a pointer other than its "
                             "dynamic-storage arguments");
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
        emitPassive(P, PassiveStmt::Assert, makeBoolLiteral(false, C.Loc),
                    nullptr, C.Loc, ProofObligationKind::Unsupported,
                    "the valid extent of " + C.Callee + "'s parameter " +
                        Extent.Base + " has no argument");
        continue;
      }
      auto Length = substParams(Extent.Length.get(), ParamMap, Ctx, EntryHeap);
      auto Contained = sliceContainment(Actual->second.get(), Length.get(),
                                        Extent.PointerType.PointeeSizeBytes,
                                        ActiveValidExtents, C.Loc);
      emitPassive(P, PassiveStmt::Assert, std::move(Contained), nullptr, C.Loc,
                  ProofObligationKind::Bounds);
      // A region write through an extent is framed by the extent itself
      // once both sides check memory against their objects.
      if (HasImplicitHeapEffect ||
          (hasUnboundedExtentWrite(*Callee, Extent.Base) &&
           !(Fn.ObjectModel && Callee->ObjectModel)))
        emitPassive(P, PassiveStmt::Assert, makeBoolLiteral(false, C.Loc),
                    nullptr, C.Loc, ProofObligationKind::Unsupported,
                    HasImplicitHeapEffect
                        ? C.Callee + " may write anywhere (it has no "
                                     "modifies), and the slice it receives "
                                     "does not bound that"
                        : C.Callee + " writes its whole slice, which needs "
                                     "memory checking on both sides "
                                     "(--check-ub)");
      auto LengthValue = asPointerOffset(Length.get());
      if (!LengthValue) {
        emitPassive(P, PassiveStmt::Assert, makeBoolLiteral(false, C.Loc),
                    nullptr, C.Loc, ProofObligationKind::Unsupported,
                    "the valid extent length of " + C.Callee + "'s parameter " +
                        Extent.Base + " is not an integer");
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
    std::vector<std::unique_ptr<VExpr>> ActualCounts;
    for (const VFootprint &M : Callee->Modifies) {
      ActualModifies.push_back(
          substParams(M.Target.get(), ParamMap, Ctx, EntryHeap, EntryHeap));
      ActualCounts.push_back(M.Count ? substParams(M.Count.get(), ParamMap, Ctx,
                                                   EntryHeap, EntryHeap)
                                     : nullptr);
    }
    std::vector<std::unique_ptr<VExpr>> CallerModifies;
    std::vector<std::unique_ptr<VExpr>> CallerCounts;
    CloneCtx CallerEntryCtx{Renames, OldState, true};
    for (const VFootprint &M : Fn.Modifies) {
      CallerModifies.push_back(cloneExpr(M.Target.get(), CallerEntryCtx));
      CallerCounts.push_back(
          M.Count ? cloneExpr(M.Count.get(), CallerEntryCtx) : nullptr);
    }
    // The cells a callee footprint covers, where they are known: a range, a
    // cell, or in the object model the object its region names.
    auto calleeFootprintBytes = [&](size_t I) -> std::optional<Region> {
      const auto *Actual = ActualModifies[I] && ActualModifies[I]->K == VExpr::Load
                               ? static_cast<const VLoadExpr *>(
                                     ActualModifies[I].get())
                               : nullptr;
      if (!Actual)
        return std::nullopt;
      const VFootprint &Declared = Callee->Modifies[I];
      if (ActualCounts[I])
        return rangeBytes(Actual->Ptr.get(), ActualCounts[I].get(),
                          Declared.ElementSize, C.Loc);
      if (!isRegionFootprint(Declared, Callee->ReferenceParams))
        return cellRegion(Actual->Ptr.get(), Actual->Ty, C.Loc);
      if (!Callee->ObjectModel)
        return std::nullopt;
      const VExpr *Base = addressRoot(
          static_cast<const VLoadExpr *>(Declared.Target.get())->Ptr.get());
      if (!Base || Base->K != VExpr::Var)
        return std::nullopt;
      const uint64_t Stride = std::max<uint64_t>(Base->Ty.PointeeSizeBytes, 1);
      for (const VValidExtent &Extent : Callee->ValidExtents)
        if (Extent.Base == static_cast<const VVarExpr *>(Base)->Name) {
          auto Length =
              substParams(Extent.Length.get(), ParamMap, Ctx, EntryHeap);
          return rangeBytes(Actual->Ptr.get(), Length.get(), Stride, C.Loc);
        }
      // A single scalar object is one heap cell.
      if (Actual->Ty.isInt() || Actual->Ty.Kind == VTypeKind::Bool ||
          Actual->Ty.Kind == VTypeKind::Ptr)
        return cellRegion(Actual->Ptr.get(), Actual->Ty, C.Loc);
      return Region{cloneVExpr(Actual->Ptr.get()),
                    addBytes(cloneVExpr(Actual->Ptr.get()),
                             std::make_unique<VLiteralExpr>(
                                 std::to_string(Stride), pointerOffsetType(),
                                 C.Loc),
                             C.Loc)};
    };

    std::set<std::string> CalleePointerParams;
    for (const auto &[Name, Ty] : Callee->Params)
      if (Ty.Kind == VTypeKind::Ptr)
        CalleePointerParams.insert(Name);
    std::set<std::string> ContainedPointerParams;
    for (const VValidExtent &Extent : Callee->ValidExtents)
      ContainedPointerParams.insert(Extent.Base);
    for (size_t I = 0; I != Callee->Preconditions.size(); ++I) {
      const VExpr *Pre = Callee->Preconditions[I].get();
      auto BoundPre = substParams(Pre, ParamMap, Ctx, EntryHeap, "", {},
                                  nullptr, &ContainedPointerParams);
      // A parameter with a declared extent is the slice machinery's.
      if (Fn.ObjectModel &&
          llvm::none_of(ContainedPointerParams, [&](const std::string &Name) {
            return referencesVar(Pre, Name);
          }))
        BoundPre = abstractValidity(std::move(BoundPre), Renames);
      BoundPre = rebaseSliceBinders(std::move(BoundPre));
      SafetyChecks Checks;
      collectSafety(Pre, &FnMap, &Callee->ValidExtents, &CalleePointerParams,
                    Checks, Fn.ObjectModel);
      groupByKind(Checks);
      for (const SafetyCheck &Check : Checks)
        emitPassive(P, PassiveStmt::Assert,
                    substParams(Check.Cond.get(), ParamMap, Ctx, EntryHeap),
                    nullptr, C.Loc, Check.Kind);
      emitMathBridge(P, BoundPre.get(), nullptr, C.Loc);
      emitPassive(P, PassiveStmt::Assert, std::move(BoundPre), nullptr, C.Loc,
                  preconditionKind(*Callee, I));
    }

    // A call within the caller's recursion cycle lowers the measure below its
    // value at the caller's entry, so assuming the callee's contract there is
    // well-founded induction.
    if (!Fn.IsSpec && !Fn.Decreases.empty() &&
        (C.CalleeIdentity == Fn.Identity ||
         Fn.RecursionGroup.count(C.CalleeIdentity)) &&
        Callee->Decreases.size() == Fn.Decreases.size()) {
      CloneCtx EntryCtx{Renames, OldState, true};
      std::vector<std::unique_ptr<VExpr>> CalleeMeasure;
      std::vector<std::unique_ptr<VExpr>> EntryMeasure;
      for (const auto &D : Callee->Decreases) {
        SafetyChecks Checks;
        collectSafety(D.get(), &FnMap, &Callee->ValidExtents,
                      &CalleePointerParams, Checks, Fn.ObjectModel);
        groupByKind(Checks);
        for (const SafetyCheck &Check : Checks)
          emitPassive(P, PassiveStmt::Assert,
                      substParams(Check.Cond.get(), ParamMap, Ctx, EntryHeap),
                      nullptr, C.Loc, Check.Kind);
        CalleeMeasure.push_back(substParams(D.get(), ParamMap, Ctx, EntryHeap));
      }
      for (const auto &D : Fn.Decreases)
        EntryMeasure.push_back(cloneExpr(D.get(), EntryCtx));
      emitPassive(P, PassiveStmt::Assert,
                  buildLexDecrease(CalleeMeasure, EntryMeasure, C.Loc), nullptr,
                  C.Loc, ProofObligationKind::Termination);
    }

    for (size_t I = 0; I < ActualModifies.size(); ++I) {
      const auto &M = ActualModifies[I];
      // A footprint names memory without reading it: only its address
      // computation must be defined.
      emitExprSafety(P,
                     M && M->K == VExpr::Load
                         ? static_cast<const VLoadExpr *>(M.get())->Ptr.get()
                         : M.get(),
                     nullptr, M->Loc, Renames);
      if (ActualCounts[I])
        emitExprSafety(P, ActualCounts[I].get(), nullptr, M->Loc, Renames);
      auto Allowed = makeBoolLiteral(false, C.Loc);
      const auto *ActualLoad = M && M->K == VExpr::Load
                                   ? static_cast<const VLoadExpr *>(M.get())
                                   : nullptr;
      if (ActualLoad) {
        const bool ActualIsRegion =
            isRegionFootprint(Callee->Modifies[I], Callee->ReferenceParams);
        if (auto Provenance = pointerProvenance(ActualLoad->Ptr.get()))
          for (const std::string &Identity : OwnedAllocationIdentities)
            Allowed = makeOr(std::move(Allowed),
                             makeEq(cloneVExpr(Provenance.get()),
                                    std::make_unique<VVarExpr>(
                                        Identity, VType::makePtr(), C.Loc),
                                    C.Loc),
                             C.Loc);
        std::optional<Region> InnerBytes;
        if (ActualCounts[I] || ActualIsRegion)
          InnerBytes = calleeFootprintBytes(I);
        // An empty range writes nothing.
        if (ActualCounts[I] && InnerBytes)
          Allowed = std::make_unique<VBinOpExpr>(
              VBinOp::Le, cloneVExpr(InnerBytes->Hi.get()),
              cloneVExpr(InnerBytes->Lo.get()), VType::makeBool(), C.Loc);
        for (size_t J = 0; J < CallerModifies.size(); ++J) {
          const auto &CallerM = CallerModifies[J];
          const auto *CallerLoad =
              CallerM && CallerM->K == VExpr::Load
                  ? static_cast<const VLoadExpr *>(CallerM.get())
                  : nullptr;
          if (!CallerLoad)
            continue;
          std::optional<Region> OuterBytes;
          if (CallerCounts[J])
            OuterBytes = rangeBytes(CallerLoad->Ptr.get(), CallerCounts[J].get(),
                                    Fn.Modifies[J].ElementSize, C.Loc);
          Allowed = makeOr(
              std::move(Allowed),
              footprintWithin(CallerLoad->Ptr.get(),
                              isRegionFootprint(Fn.Modifies[J],
                                                Fn.ReferenceParams),
                              OuterBytes, ActualLoad->Ptr.get(), ActualIsRegion,
                              ActualCounts[I] != nullptr, InnerBytes, C.Loc),
              C.Loc);
        }
      }
      emitPassive(P, PassiveStmt::Assert, std::move(Allowed), nullptr, C.Loc,
                  ProofObligationKind::Frame);
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
                  nullptr, C.Loc, ProofObligationKind::Frame);
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
          ActualCounts[I] ||
          (isRegionFootprint(Callee->Modifies[I], Callee->ReferenceParams) &&
           !hasPointerProvenance(
               static_cast<const VLoadExpr *>(ActualModifies[I].get())
                   ->Ptr.get())))
        CanFrameExactly = false;
    // A region footprint is its actual's object: the callee's extent, or one
    // object; in the object model the callee writes nowhere else.
    std::vector<Region> CallRegions;
    bool CanFrameRegions = Fn.ObjectModel && Callee->ObjectModel &&
                           !CanFrameExactly && !ActualModifies.empty() &&
                           !HasImplicitHeapEffect;
    for (size_t I = 0; CanFrameRegions && I < ActualModifies.size(); ++I) {
      std::optional<Region> Bytes;
      if (ActualModifies[I] && ActualModifies[I]->K == VExpr::Load &&
          !hasPointerProvenance(
              static_cast<const VLoadExpr *>(ActualModifies[I].get())
                  ->Ptr.get()))
        Bytes = calleeFootprintBytes(I);
      if (!Bytes) {
        CanFrameRegions = false;
        break;
      }
      CallRegions.push_back(std::move(*Bytes));
    }
    const bool OnlyCells =
        llvm::all_of(CallRegions, [](const Region &R) { return R.Cell; });
    if (CanFrameRegions && OnlyCells) {
      // Each cell gets an unknown value and every other cell keeps its own.
      std::string PreviousHeap = EntryHeap;
      for (const Region &R : CallRegions) {
        std::string NextHeap = bump(VHeapName);
        auto Fresh = std::make_unique<VVarExpr>(bump("__call_heap_value"),
                                                *R.Cell, C.Loc);
        emitPassive(P, PassiveStmt::Assume,
                    std::make_unique<VHeapStoreExpr>(PreviousHeap, NextHeap,
                                                     cloneVExpr(R.Lo.get()),
                                                     std::move(Fresh), C.Loc));
        PreviousHeap = NextHeap;
      }
      Renames[VHeapName] = PreviousHeap;
    } else if (CanFrameRegions) {
      std::string NextHeap = bump(VHeapName);
      emitPassive(P, PassiveStmt::Assume,
                  heapFrame(EntryHeap, NextHeap, CallRegions, C.Loc));
      Renames[VHeapName] = NextHeap;
    } else if ((!ActualModifies.empty() && !CanFrameExactly) ||
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

    const size_t FirstPost = P.Stmts.size();
    for (const auto &Post : Callee->Postconditions) {
      auto PS = std::make_unique<PassiveStmt>();
      PS->K = PassiveStmt::Assume;
      PS->Cond = rebaseSliceBinders(substParams(Post.get(), PostParamMap, Ctx,
                                                EntryHeap, "", {}, &ParamMap));
      P.Stmts.push_back(std::move(PS));
    }
    if (Callee->IsTrusted && P.Stmts.size() > FirstPost) {
      P.Stmts[FirstPost]->TrustedCallee = Callee->Name;
      P.Stmts[FirstPost]->PostClauses = P.Stmts.size() - FirstPost;
      P.Stmts[FirstPost]->CallLoc = C.Loc;
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
                    Active.get(), St.Loc, ProofObligationKind::Unsupported,
                    "storing a pointer to local or dynamic storage in memory, "
                    "where its lifetime is not tracked");
        break;
      }
      std::unique_ptr<VExpr> PointerCell =
          Val->Ty.Kind == VTypeKind::Ptr ? cloneVExpr(Ptr.get()) : nullptr;
      const VType StoredPointerType = Val->Ty;
      if (AccessCondition) {
        emitExprSafety(P, AccessCondition.get(), Active.get(), St.Loc, Renames,
                       false, St.AccessCondition.get());
        emitPassive(P, PassiveStmt::Assert, std::move(AccessCondition),
                    Active.get(), St.Loc, ProofObligationKind::Bounds);
      }
      auto StoreSafety = nonNullSafety(Ptr.get(), St.Loc, Fn.ObjectModel);
      emitPassive(P, PassiveStmt::Assert, cloneExpr(StoreSafety.get(), Ctx),
                  Active.get(), St.Loc, ProofObligationKind::Dereference);
      auto Allowed = makeBoolLiteral(false, St.Loc);
      CloneCtx EntryCtx{Renames, OldState, true};
      for (const VFootprint &M : Fn.Modifies)
        if (const auto *Load = M.Target && M.Target->K == VExpr::Load
                                   ? static_cast<const VLoadExpr *>(
                                         M.Target.get())
                                   : nullptr) {
          auto DeclaredPtr = cloneExpr(Load->Ptr.get(), EntryCtx);
          std::optional<Region> Bytes;
          if (M.Count) {
            auto Count = cloneExpr(M.Count.get(), EntryCtx);
            Bytes = rangeBytes(DeclaredPtr.get(), Count.get(), M.ElementSize,
                               St.Loc);
          }
          auto EffectivePtr = resolveReferenceAddress(Ptr.get());
          const bool Region = isRegionFootprint(M, Fn.ReferenceParams);
          Allowed = makeOr(
              std::move(Allowed),
              footprintWithin(DeclaredPtr.get(), Region, Bytes,
                              EffectivePtr.get(), false, false, std::nullopt,
                              St.Loc),
              St.Loc);
          // A region is its parameter's object: a store at any address in
          // it, such as through a pointer walking the object, is inside.
          const VExpr *Root = addressRoot(Load->Ptr.get());
          // So is a store through a pointer whose origin is that object: its
          // access check keeps it there.
          if (Fn.ObjectModel && Region && Root && Root->K == VExpr::Var) {
            const std::string &Param =
                static_cast<const VVarExpr *>(Root)->Name;
            const VExpr *StoreRoot = addressRoot(St.Ptr.get());
            if (auto Origins = pointerOrigins(StoreRoot);
                Origins && llvm::is_contained(*Origins, Param)) {
              auto Term =
                  Origins->size() > 1 ? pointerOriginTerm(StoreRoot) : nullptr;
              if (Origins->size() == 1)
                Allowed = makeBoolLiteral(true, St.Loc);
              else if (Term)
                Allowed = makeOr(std::move(Allowed),
                                 makeEq(cloneExpr(Term.get(), Ctx),
                                        originIdentity(Param, St.Loc), St.Loc),
                                 St.Loc);
            }
          }
          if (Fn.ObjectModel && Region && Root && Root->K == VExpr::Var)
            if (auto Object = parameterRegion(
                    static_cast<const VVarExpr *>(Root)->Name, Renames,
                    St.Loc))
              Allowed = makeOr(
                  std::move(Allowed),
                  makeAnd(std::make_unique<VBinOpExpr>(
                              VBinOp::Le, std::move(Object->Lo),
                              cloneVExpr(EffectivePtr.get()),
                              VType::makeBool(), St.Loc),
                          std::make_unique<VBinOpExpr>(
                              VBinOp::Lt, cloneVExpr(EffectivePtr.get()),
                              std::move(Object->Hi), VType::makeBool(),
                              St.Loc),
                          St.Loc),
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
                  St.Loc, ProofObligationKind::Frame);
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
                    Active.get(), A.Loc, ProofObligationKind::Unsupported,
                    "an allocation without a lifetime identity");
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
      emitPassive(P, PassiveStmt::Assume,
                  belowGlobals(Pointer.get(), A.SizeBytes, A.Loc), Active.get(),
                  A.Loc);
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
            Active.get(), F.Loc, ProofObligationKind::Deallocation);
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
                  F.Loc, ProofObligationKind::Deallocation);
      auto Owned = cloneVExpr(IsNull.get());
      for (const std::string &Identity : OwnedAllocationIdentities)
        Owned = makeOr(std::move(Owned),
                       makeEq(cloneVExpr(Provenance.get()),
                              std::make_unique<VVarExpr>(
                                  Identity, VType::makePtr(), F.Loc),
                              F.Loc),
                       F.Loc);
      emitPassive(P, PassiveStmt::Assert, std::move(Owned), Active.get(), F.Loc,
                  ProofObligationKind::Deallocation);
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
      const VExpr *ThenEntryGuard = ThenActive.get();
      const VExpr *ElseEntryGuard = ElseActive.get();
      for (const auto &TS : I.Then)
        processStmt(*TS, ThenP, ThenRenames, ThenActive);
      for (const auto &ES : I.Else)
        processStmt(*ES, ElseP, ElseRenames, ElseActive);
      const bool ThenKeepsPaths = ThenActive.get() == ThenEntryGuard;
      const bool ElseKeepsPaths = ElseActive.get() == ElseEntryGuard;
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
      // (A && c) || (A && !c) is A: keep A unless a branch left a path.
      if (ThenKeepsPaths && ElseKeepsPaths)
        break;
      if (isFalseLiteral(ThenActive.get()))
        Active = std::move(ElseActive);
      else if (isFalseLiteral(ElseActive.get()))
        Active = std::move(ThenActive);
      else
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
      CloneCtx EntryCtx{Renames, OldState, false};
      for (const auto &Inv : W.Invariants) {
        auto BoundInv = cloneExpr(Inv.get(), EntryCtx);
        emitExprSafety(P, BoundInv.get(), Active.get(), Inv->Loc, Renames,
                       false, Inv.get());
        emitPassive(P, PassiveStmt::Assert, std::move(BoundInv), Active.get(),
                    Inv->Loc, ProofObligationKind::InvariantEntry);
      }

      std::set<std::string> Modified;
      for (const auto &Body : W.Body)
        collectModified(*Body, Modified);
      // A loop in the object model writes only the objects its stores and
      // calls reach; the rest of the heap keeps its values.
      std::vector<Region> WriteRegions;
      bool Framed = Fn.ObjectModel && Modified.count(VHeapName) &&
                    loopWriteRegions(W.Body, Renames, WriteRegions);
      // Every store and call in the loop is checked against the function's
      // own frame, so that frame bounds what the loop writes too; with both,
      // only cells in both may change.
      std::vector<Region> FunctionRegions;
      const bool AlsoFunctionFramed =
          Framed && functionFrameRegions(Renames, W.Loc, FunctionRegions);
      if (!Framed && Fn.ObjectModel && Modified.count(VHeapName)) {
        WriteRegions.clear();
        Framed = functionFrameRegions(Renames, W.Loc, WriteRegions);
      }
      std::string LoopEntryHeap;
      if (!W.Modifies.empty() && Modified.count(VHeapName))
        if (auto It = Renames.find(VHeapName); It != Renames.end())
          LoopEntryHeap = It->second;
      for (const std::string &Name : Modified) {
        auto Previous = Renames.find(Name);
        if (Previous == Renames.end())
          continue;
        const std::string PreviousName = Previous->second;
        const std::string HeadName = bump(Name);
        Renames[Name] = HeadName;
        emitInactiveFrame(P, PreviousName, HeadName, typeForName(Name),
                          Active.get(), W.Loc);
        if (Framed && Name == VHeapName) {
          const bool OnlyCells =
              !WriteRegions.empty() &&
              llvm::all_of(WriteRegions,
                           [](const Region &R) { return R.Cell.has_value(); });
          if (AlsoFunctionFramed)
            emitPassive(
                P, PassiveStmt::Assume,
                heapFrame(PreviousName, HeadName, FunctionRegions, W.Loc),
                Active.get(), W.Loc);
          if (!OnlyCells) {
            emitPassive(P, PassiveStmt::Assume,
                        heapFrame(PreviousName, HeadName, WriteRegions, W.Loc),
                        Active.get(), W.Loc);
            continue;
          }
          // Each written cell holds an unknown value; every other cell keeps
          // its value from before the loop.
          std::string Before = PreviousName;
          for (size_t I = 0; I != WriteRegions.size(); ++I) {
            const std::string After =
                I + 1 == WriteRegions.size() ? HeadName : bump(VHeapName);
            auto Fresh = std::make_unique<VVarExpr>(
                bump("__loop_heap_value"), *WriteRegions[I].Cell, W.Loc);
            emitPassive(P, PassiveStmt::Assume,
                        std::make_unique<VHeapStoreExpr>(
                            Before, After, cloneVExpr(WriteRegions[I].Lo.get()),
                            std::move(Fresh), W.Loc),
                        Active.get(), W.Loc);
            Before = After;
          }
        }
      }

      CloneCtx HeadCtx{Renames, OldState, false};
      if (!LoopEntryHeap.empty()) {
        // Every iteration starts with the cells outside the declared
        // footprints unchanged since the loop began.
        if (auto Regions = loopFootprintRegions(W, HeadCtx, Renames))
          emitPassive(P, PassiveStmt::Assume,
                      heapFrame(LoopEntryHeap, Renames[VHeapName], *Regions,
                                W.Loc),
                      Active.get(), W.Loc);
      }
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
        emitExprSafety(P, Bound.get(), IterationActive.get(), Decrease->Loc,
                       Renames, false, Decrease.get());
        OldDecreases.push_back(std::move(Bound));
      }

      auto BodyRenames = Renames;
      auto BodyActive = cloneVExpr(IterationActive.get());
      PassiveProgram BodyP;
      const size_t ReturnsBefore = ReturnGuards.size();
      LoopFrames.push_back({&W, &OldDecreases, {}, LoopEntryHeap});
      for (const auto &BS : W.Body)
        processStmt(*BS, BodyP, BodyRenames, BodyActive);
      LoopFrame Frame = std::move(LoopFrames.back());
      LoopFrames.pop_back();
      appendProgram(P, BodyP);

      for (const auto &Inv : W.Invariants) {
        CloneCtx ACtx{BodyRenames, OldState, false};
        auto BoundInv = cloneExpr(Inv.get(), ACtx);
        emitExprSafety(P, BoundInv.get(), BodyActive.get(), Inv->Loc,
                       BodyRenames, false, Inv.get());
        emitPassive(P, PassiveStmt::Assert, std::move(BoundInv),
                    BodyActive.get(), Inv->Loc,
                    ProofObligationKind::InvariantPreserved);
      }
      emitLoopFrameCheck(P, W, LoopEntryHeap, BodyRenames, BodyActive.get());

      if (!W.Decreases.empty()) {
        CloneCtx AfterCtx{BodyRenames, OldState, false};
        std::vector<std::unique_ptr<VExpr>> NewDecreases;
        for (const auto &Decrease : W.Decreases) {
          auto Bound = cloneExpr(Decrease.get(), AfterCtx);
          emitExprSafety(P, Bound.get(), BodyActive.get(), Decrease->Loc,
                         BodyRenames, false, Decrease.get());
          NewDecreases.push_back(std::move(Bound));
        }
        emitPassive(P, PassiveStmt::Assert,
                    buildLexDecrease(NewDecreases, OldDecreases, W.Loc),
                    BodyActive.get(), W.Loc, ProofObligationKind::Termination);
      }

      emitTrace(PassiveTraceKind::Loop, "exit", Active.get(), W.Loc);
      std::vector<const VExpr *> Returns;
      for (size_t I = ReturnsBefore; I != ReturnGuards.size(); ++I)
        Returns.push_back(ReturnGuards[I].get());
      if (Frame.BreakGuards.empty() && Returns.empty()) {
        emitPassive(P, PassiveStmt::Assume, makeNot(std::move(Choice), W.Loc),
                    Active.get(), W.Loc);
        emitPassive(P, PassiveStmt::Assume, makeNot(std::move(HeadCond), W.Loc),
                    Active.get(), W.Loc);
        break;
      }
      // Exit paths keep their exit state to the end of the body, so the
      // iteration choice selects between head and body-end state.
      auto Exits = makeAnd(makeNot(cloneVExpr(Choice.get()), W.Loc),
                           makeNot(std::move(HeadCond), W.Loc), W.Loc);
      for (const auto &Guard : Frame.BreakGuards)
        Exits = makeOr(std::move(Exits), cloneVExpr(Guard.get()), W.Loc);
      std::unique_ptr<VExpr> Returned = makeBoolLiteral(false, W.Loc);
      for (const VExpr *Guard : Returns) {
        Exits = makeOr(std::move(Exits), cloneVExpr(Guard), W.Loc);
        Returned = makeOr(std::move(Returned), cloneVExpr(Guard), W.Loc);
      }
      emitPassive(P, PassiveStmt::Assume, std::move(Exits), Active.get(),
                  W.Loc);
      for (const auto &[Name, BodyVersion] : BodyRenames) {
        auto Head = Renames.find(Name);
        if (Head == Renames.end() || Head->second == BodyVersion)
          continue;
        const VType Ty = typeForName(Name);
        const std::string HeadVersion = Head->second;
        std::string Merged = bump(Name);
        Renames[Name] = Merged;
        auto MergeExpr = std::make_unique<VConditionalExpr>(
            cloneVExpr(Choice.get()),
            std::make_unique<VVarExpr>(BodyVersion, Ty, W.Loc),
            std::make_unique<VVarExpr>(HeadVersion, Ty, W.Loc), Ty, W.Loc);
        emitPassive(P, PassiveStmt::Assume,
                    makeEq(std::make_unique<VVarExpr>(Merged, Ty, W.Loc),
                           std::move(MergeExpr), W.Loc),
                    Active.get(), W.Loc);
        emitInactiveFrame(P, HeadVersion, Merged, Ty, Active.get(), W.Loc);
      }
      if (!Returns.empty())
        Active = makeAnd(std::move(Active), makeNot(std::move(Returned), W.Loc),
                         W.Loc);
      break;
    }
    case VStmt::Break: {
      if (LoopFrames.empty()) {
        emitPassive(P, PassiveStmt::Assert, makeBoolLiteral(false, S.Loc),
                    Active.get(), S.Loc, ProofObligationKind::Unsupported,
                    "a break outside the loop it would leave, such as in the "
                    "first iteration of a do loop");
        break;
      }
      emitTrace(PassiveTraceKind::Loop, "break", Active.get(), S.Loc);
      LoopFrames.back().BreakGuards.push_back(cloneVExpr(Active.get()));
      Active = makeBoolLiteral(false, S.Loc);
      break;
    }
    case VStmt::Continue: {
      if (LoopFrames.empty()) {
        emitPassive(P, PassiveStmt::Assert, makeBoolLiteral(false, S.Loc),
                    Active.get(), S.Loc, ProofObligationKind::Unsupported,
                    "a continue outside the loop it would continue, such as "
                    "in the first iteration of a do loop");
        break;
      }
      // The iteration ends: check the invariant and measure here.
      const LoopFrame &Frame = LoopFrames.back();
      emitTrace(PassiveTraceKind::Loop, "continue", Active.get(), S.Loc);
      CloneCtx ContinueCtx{Renames, OldState, false};
      for (const auto &Inv : Frame.Loop->Invariants) {
        auto BoundInv = cloneExpr(Inv.get(), ContinueCtx);
        emitExprSafety(P, BoundInv.get(), Active.get(), Inv->Loc, Renames,
                       false, Inv.get());
        emitPassive(P, PassiveStmt::Assert, std::move(BoundInv), Active.get(),
                    Inv->Loc, ProofObligationKind::InvariantPreserved);
      }
      emitLoopFrameCheck(P, *Frame.Loop, Frame.EntryHeap, Renames,
                         Active.get());
      if (!Frame.Loop->Decreases.empty()) {
        std::vector<std::unique_ptr<VExpr>> NewDecreases;
        for (const auto &Decrease : Frame.Loop->Decreases) {
          auto Bound = cloneExpr(Decrease.get(), ContinueCtx);
          emitExprSafety(P, Bound.get(), Active.get(), Decrease->Loc, Renames,
                         false, Decrease.get());
          NewDecreases.push_back(std::move(Bound));
        }
        emitPassive(P, PassiveStmt::Assert,
                    buildLexDecrease(NewDecreases, *Frame.OldDecreases, S.Loc),
                    Active.get(), S.Loc, ProofObligationKind::Termination);
      }
      Active = makeBoolLiteral(false, S.Loc);
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
      // Proved here, a fact from here on: that is what makes it a proof step.
      auto Fact = cloneVExpr(Cond.get());
      emitPassive(P, PassiveStmt::Assert, std::move(Cond), Active.get(), A.Loc,
                  ProofObligationKind::Assertion);
      emitPassive(P, PassiveStmt::Assume, std::move(Fact), Active.get(), A.Loc);
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
        if (!CallStmt->TrustedCallee.empty())
          CallStmt->CallGuard = cloneVExpr(Active.get());
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
      if (Fn.ObjectModel &&
          (A.ProofKind == ProofObligationKind::Dereference ||
           A.ProofKind == ProofObligationKind::Initialization))
        Cond = abstractValidity(std::move(Cond), Renames);
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