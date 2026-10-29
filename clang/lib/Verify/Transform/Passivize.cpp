//===--- Passivize.cpp ----------------------------------------------------===//
#include "Passivize.h"
#include "Origins.h"
#include "SpecInline.h"
#include "SubobjectBounds.h"
#include "UBChecks.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/STLFunctionalExtras.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/SaveAndRestore.h"
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
  if (Copy && E) {
    Copy->BeginLoc = E->BeginLoc;
    Copy->EndLoc = E->EndLoc;
  }
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
  case VExpr::Require: {
    const auto *R = static_cast<const VRequireExpr *>(E);
    return std::make_unique<VRequireExpr>(cloneExpr(R->Cond.get(), Ctx),
                                          R->ProofKind, R->Loc);
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

/// Whether a value of type \p Ty lies in its enumeration's value range: a
/// machine value does, since only a conversion can produce one outside it and
/// executable and proof code check every conversion. A spec converts without
/// a check.
static bool keepsEnumRange(const VType &Ty) {
  return !Ty.EnumMin.empty() && Ty.IntMode == VIntMode::Machine;
}

/// \p Value, of an integer type or bool, lies in \p Enum's value range.
static std::unique_ptr<VExpr> inEnumRange(const VExpr *Value, const VType &Enum,
                                          SourceLocation Loc) {
  VType MathTy = VType::makeInt(VIntMode::Math, 64, true);
  std::unique_ptr<VExpr> Exact;
  if (Value->Ty.Kind == VTypeKind::Bool) {
    Exact = std::make_unique<VConditionalExpr>(
        cloneVExpr(Value), std::make_unique<VLiteralExpr>(1, MathTy, Loc),
        std::make_unique<VLiteralExpr>(0, MathTy, Loc), MathTy, Loc);
  } else if (Value->Ty.IntMode == VIntMode::Math) {
    Exact = cloneVExpr(Value);
  } else {
    Exact = mathCast(Value);
  }
  auto AtLeast = std::make_unique<VBinOpExpr>(
      VBinOp::Ge, cloneVExpr(Exact.get()),
      std::make_unique<VLiteralExpr>(Enum.EnumMin, MathTy, Loc),
      VType::makeBool(), Loc);
  auto Below = std::make_unique<VBinOpExpr>(
      VBinOp::Lt, std::move(Exact),
      std::make_unique<VLiteralExpr>(Enum.EnumMax, MathTy, Loc),
      VType::makeBool(), Loc);
  return makeAnd(std::move(AtLeast), std::move(Below), Loc);
}

/// The converted value lies in the target enumeration's value range.
static std::unique_ptr<VExpr> enumValueInRange(const VCastExpr *C) {
  return inEnumRange(C->Inner.get(), C->Ty, C->Loc);
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
/// a parameter's entry object (its declared extent, else one object of its
/// pointee type, an entry with no length in Extents) or a global. Null when
/// an origin is not such an object.
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
      // The object is measured in its own elements: a pointer into a
      // subobject (a member array) has a smaller type than its origin's.
      const uint64_t ObjectStride =
          Extent ? Extent->PointerType.PointeeSizeBytes : Stride;
      if (Extent && Extent->Length) {
        VOldExpr Length(cloneVExpr(Extent->Length.get()), Extent->Length->Ty,
                        Loc);
        Bytes = scaledExtent(&Length, ObjectStride, Loc);
      } else if (Extent && ObjectStride > 0) {
        Bytes = std::make_unique<VLiteralExpr>(std::to_string(ObjectStride),
                                               pointerOffsetType(), Loc);
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
  case VExpr::Require:
    return referencesVar(static_cast<const VRequireExpr *>(E)->Cond.get(),
                         Name);
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
  case VExpr::Require:
    return scalarDynamicExprSafe(
        static_cast<const VRequireExpr *>(E)->Cond.get(), Param);
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

/// Whether a pointer-typed expression may hold an address derived from one
/// of the aliases.
static bool pointerFromAliases(const VExpr *E,
                               const std::set<std::string> &Aliases) {
  return E && E->Ty.Kind == VTypeKind::Ptr && referencesAnyAlias(E, Aliases);
}

/// The pointer variables of a body that may hold an address derived from
/// the aliases: those assigned one, to a fixpoint.
static void
collectRecordAliases(const std::vector<std::unique_ptr<VStmt>> &Body,
                     std::set<std::string> &Aliases, bool &Changed) {
  for (const auto &S : Body) {
    switch (S->K) {
    case VStmt::Assign: {
      const auto &A = static_cast<const VAssignStmt &>(*S);
      if (pointerFromAliases(A.Value.get(), Aliases) &&
          Aliases.insert(A.Target).second)
        Changed = true;
      break;
    }
    case VStmt::If: {
      const auto &I = static_cast<const VIfStmt &>(*S);
      collectRecordAliases(I.Then, Aliases, Changed);
      collectRecordAliases(I.Else, Aliases, Changed);
      break;
    }
    case VStmt::While:
      collectRecordAliases(static_cast<const VWhileStmt &>(*S).Body, Aliases,
                           Changed);
      break;
    case VStmt::Seq:
      collectRecordAliases(static_cast<const VSeqStmt &>(*S).Stmts, Aliases,
                           Changed);
      break;
    case VStmt::GhostBlock:
      collectRecordAliases(static_cast<const VGhostBlockStmt &>(*S).Body,
                           Aliases, Changed);
      break;
    default:
      break;
    }
  }
}

static bool
keepsNoAddress(const VFunction &Fn, const std::string &Param, bool AllowExtent,
               const FunctionMap &FnMap,
               std::set<std::pair<std::string, std::string>> &ActiveScans);

/// Whether a statement keeps no address derived from the aliases beyond the
/// call: none is stored in memory, returned, freed, or passed to a callee
/// that keeps it. An address converted to an integer is no escape, since no
/// integer becomes a pointer again (the frontend rejects those casts).
static bool
recordStmtSafe(const VStmt &S, const std::set<std::string> &Aliases,
               const FunctionMap &FnMap,
               std::set<std::pair<std::string, std::string>> &ActiveScans) {
  auto Each = [&](const std::vector<std::unique_ptr<VStmt>> &Body) {
    return llvm::all_of(Body, [&](const std::unique_ptr<VStmt> &Nested) {
      return recordStmtSafe(*Nested, Aliases, FnMap, ActiveScans);
    });
  };
  switch (S.K) {
  case VStmt::Store:
    return !pointerFromAliases(static_cast<const VStoreStmt &>(S).Value.get(),
                               Aliases);
  case VStmt::Allocate: {
    // A local object of the callee's own keeps no address unless it is
    // initialized with one; one from new makes it UsesDynamicStorage, which
    // keepsNoAddress rejects before it looks at a statement.
    const auto &A = static_cast<const VAllocateStmt &>(S);
    return A.IsAutomatic && !pointerFromAliases(A.Initializer.get(), Aliases);
  }
  case VStmt::Free:
    return false;
  case VStmt::If: {
    const auto &I = static_cast<const VIfStmt &>(S);
    return Each(I.Then) && Each(I.Else);
  }
  case VStmt::While:
    return Each(static_cast<const VWhileStmt &>(S).Body);
  case VStmt::Call: {
    const auto &C = static_cast<const VCallStmt &>(S);
    auto CalleeIt = FnMap.find(C.CalleeIdentity);
    if (CalleeIt == FnMap.end())
      return false;
    const VFunction &Callee = *CalleeIt->second;
    // The function passing an address proved that the callee's object or
    // extent lies in its own, so the callee need only keep none, returning
    // one included.
    for (unsigned I = 0; I < C.Args.size(); ++I)
      if (pointerFromAliases(C.Args[I].get(), Aliases) &&
          (I >= Callee.Params.size() ||
           Callee.Params[I].second.Kind != VTypeKind::Ptr ||
           !keepsNoAddress(Callee, Callee.Params[I].first,
                           /*AllowExtent=*/true, FnMap, ActiveScans)))
        return false;
    return true;
  }
  case VStmt::Return:
    return !pointerFromAliases(static_cast<const VReturnStmt &>(S).Value.get(),
                               Aliases);
  case VStmt::Seq:
    return Each(static_cast<const VSeqStmt &>(S).Stmts);
  case VStmt::GhostBlock:
    return Each(static_cast<const VGhostBlockStmt &>(S).Body);
  case VStmt::Assign:
  case VStmt::Assert:
  case VStmt::Assume:
  case VStmt::ContractAssert:
  case VStmt::EndLifetime:
  case VStmt::Havoc:
  case VStmt::RevealWithFuel:
  case VStmt::HideSpec:
  case VStmt::RevealSpec:
  case VStmt::Break:
  case VStmt::Continue:
    return true;
  }
  return false;
}

/// Whether Fn keeps no pointer into the object its parameter Param addresses
/// beyond the call. Fn is verified in the object model, so every access
/// through Param, at whatever field or element, is proved to lie in its
/// object (or its extent, which only a caller that proved the extent inside
/// its own object may give, AllowExtent); what remains is that no address
/// derived from it escapes.
static bool
keepsNoAddress(const VFunction &Fn, const std::string &Param, bool AllowExtent,
               const FunctionMap &FnMap,
               std::set<std::pair<std::string, std::string>> &ActiveScans) {
  if (Fn.IsSpec || Fn.IsProof || Fn.IsExternalContract ||
      Fn.UsesDynamicStorage || !Fn.ObjectModel ||
      (!AllowExtent &&
       llvm::any_of(Fn.ValidExtents, [&](const VValidExtent &Extent) {
         return Extent.Base == Param;
       })))
    return false;
  // An escape is a finite path to a statement that keeps an address, so a
  // scan that reaches itself again, through recursion, may assume none.
  const auto Key = std::make_pair(Fn.Identity, Param);
  if (!ActiveScans.insert(Key).second)
    return true;
  std::set<std::string> Aliases = {Param};
  for (bool Changed = true; Changed;) {
    Changed = false;
    collectRecordAliases(Fn.Body, Aliases, Changed);
  }
  bool Safe = true;
  for (const auto &S : Fn.Body)
    Safe = Safe && recordStmtSafe(*S, Aliases, FnMap, ActiveScans);
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
static constexpr const char *OutParameterNote =
    "binding a reference or pointer parameter to storage that is not "
    "initialized, which the callee may read before writing it";
static constexpr const char *UninitializedResultNote =
    "returning a pointer to storage that is not initialized, since callers "
    "read a returned pointer's storage as initialized";

/// \p E with every application of \p Op taken to hold.
static std::unique_ptr<VExpr> assumingHolds(const VExpr *E, VUnaryOp Op) {
  auto Out = cloneVExpr(E);
  std::function<void(std::unique_ptr<VExpr> &)> Replace =
      [&](std::unique_ptr<VExpr> &Slot) {
        if (Slot->K == VExpr::UnaryOp &&
            static_cast<const VUnaryOpExpr &>(*Slot).Op == Op) {
          Slot = makeBoolLiteral(true, Slot->Loc);
          return;
        }
        forEachVExprChildSlot(Slot.get(), Replace);
      };
  Replace(Out);
  return Out;
}

static bool mentionsUnary(const VExpr *E, VUnaryOp Op) {
  if (!E)
    return false;
  if (E->K == VExpr::UnaryOp &&
      static_cast<const VUnaryOpExpr *>(E)->Op == Op)
    return true;
  bool Found = false;
  forEachVExprChild(E, [&](const VExpr *Child) {
    Found = Found || mentionsUnary(Child, Op);
  });
  return Found;
}

/// A generated validity clause asks for valid and initialized storage. C++
/// asks for the first; a function is verified as reading its pointer
/// parameters' storage, and its callers its pointer result's, as
/// initialized, which C++ does not require. Where such a clause is checked,
/// the two are separate obligations, and failing the second stands for a
/// construct the verifier does not model. Both predicates occur positively,
/// so the two parts together are the clause.
static std::vector<std::tuple<ProofObligationKind, std::unique_ptr<VExpr>,
                              std::string>>
checkedClause(ProofObligationKind Kind, std::unique_ptr<VExpr> Clause,
              const char *InitializationNote) {
  std::vector<std::tuple<ProofObligationKind, std::unique_ptr<VExpr>,
                         std::string>>
      Parts;
  if (Kind != ProofObligationKind::PointerValidity ||
      !mentionsUnary(Clause.get(), VUnaryOp::InitializedPtr)) {
    Parts.emplace_back(Kind, std::move(Clause), "");
    return Parts;
  }
  Parts.emplace_back(ProofObligationKind::PointerValidity,
                     assumingHolds(Clause.get(), VUnaryOp::InitializedPtr),
                     "");
  Parts.emplace_back(ProofObligationKind::Unsupported,
                     assumingHolds(Clause.get(), VUnaryOp::ValidPtr),
                     InitializationNote);
  return Parts;
}

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
static bool
isRegionFootprint(const VFootprint &F,
                  const std::set<std::string> &ScalarReferenceParams) {
  if (F.Count)
    return false;
  const VExpr *E = F.Target.get();
  if (!E || E->K != VExpr::Load)
    return true;
  const VExpr *Ptr = static_cast<const VLoadExpr *>(E)->Ptr.get();
  while (Ptr && Ptr->K == VExpr::Cast)
    Ptr = static_cast<const VCastExpr *>(Ptr)->Inner.get();
  if (Ptr && Ptr->K == VExpr::Var &&
      ScalarReferenceParams.count(static_cast<const VVarExpr *>(Ptr)->Name))
    return false;
  return !Ptr || Ptr->K == VExpr::Var;
}

static bool hasUnboundedExtentWrite(const VFunction &Fn,
                                    const std::string &Base) {
  for (const VFootprint &Modify : Fn.Modifies) {
    if (!Modify.Target || Modify.Target->K != VExpr::Load ||
        !isRegionFootprint(Modify, Fn.ScalarReferenceParams))
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

static std::unique_ptr<VExpr>
initializedSafety(const VExpr *Ptr, SourceLocation Loc,
                  bool ObjectModel = false,
                  const std::set<std::string> *OutParameters = nullptr) {
  const VExpr *Base = pointerBase(Ptr);
  if (!Base)
    return makeBoolLiteral(false, Loc);
  if (isGlobalCell(Base))
    return makeBoolLiteral(true, Loc);
  // An out-parameter's storage is initialized where the function wrote it.
  if (OutParameters && Base->K == VExpr::Var &&
      OutParameters->count(static_cast<const VVarExpr *>(Base)->Name))
    return std::make_unique<VUnaryOpExpr>(
        VUnaryOp::InitializedPtr, cloneVExpr(Ptr), VType::makeBool(), Loc);
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

/// The definedness of the arithmetic operation \p E itself, its operands
/// taken as they are.
static void addOperationSafety(const VExpr *E, SafetyChecks &Out) {
  if (E->K == VExpr::UnaryOp) {
    const auto *U = static_cast<const VUnaryOpExpr *>(E);
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
  if (E->K != VExpr::BinOp)
    return;
  const auto *B = static_cast<const VBinOpExpr *>(E);
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
          std::make_unique<VLiteralExpr>(signedLimit(B->Lhs->Ty.BitWidth, true),
                                         B->Lhs->Ty, B->Loc),
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
}

static void
collectSafetyImpl(const VExpr *E, const FunctionMap *FnMap,
                  const std::vector<VValidExtent> *ValidExtents,
                  const std::set<std::string> *PointerParams, SafetyChecks &Out,
                  bool ObjectModel, const std::vector<VValidExtent> *OriginExtents,
                  const std::set<std::string> *OutParameters);

/// The definedness checks of \p E. A check made at an operation's anchor
/// (its operator) spans the operation, as a diagnostic underlines it.
static void
collectSafety(const VExpr *E, const FunctionMap *FnMap,
              const std::vector<VValidExtent> *ValidExtents,
              const std::set<std::string> *PointerParams, SafetyChecks &Out,
              bool ObjectModel = false,
              const std::vector<VValidExtent> *OriginExtents = nullptr,
              const std::set<std::string> *OutParameters = nullptr) {
  const size_t Before = Out.size();
  collectSafetyImpl(E, FnMap, ValidExtents, PointerParams, Out, ObjectModel,
                    OriginExtents, OutParameters);
  if (!E)
    return;
  for (size_t I = Before; I != Out.size(); ++I) {
    VExpr *Cond = Out[I].Cond.get();
    if (Cond && Cond->Loc == E->Loc && Cond->BeginLoc == Cond->Loc &&
        Cond->EndLoc == Cond->Loc) {
      Cond->BeginLoc = E->BeginLoc;
      Cond->EndLoc = E->EndLoc;
    }
  }
}

static void
collectSafetyImpl(const VExpr *E, const FunctionMap *FnMap,
                  const std::vector<VValidExtent> *ValidExtents,
                  const std::set<std::string> *PointerParams, SafetyChecks &Out,
                  bool ObjectModel, const std::vector<VValidExtent> *OriginExtents,
                  const std::set<std::string> *OutParameters) {
  auto Collect = [&](const VExpr *Sub, SafetyChecks &Into) {
    collectSafety(Sub, FnMap, ValidExtents, PointerParams, Into, ObjectModel,
                  OriginExtents, OutParameters);
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
      SafetyChecks Difference;
      addSafety(Difference, ProofObligationKind::PointerDifference,
                makeAnd(nonNullSafety(LeftBase, B->Loc, ObjectModel),
                        nonNullSafety(RightBase, B->Loc, ObjectModel), B->Loc),
                B->Loc);
      auto [OriginKind, SameOrigin] =
          samePointerDifferenceOrigin(B->Lhs.get(), B->Rhs.get(), B->Loc);
      const bool Known =
          pointerOriginTerm(B->Lhs.get()) && pointerOriginTerm(B->Rhs.get());
      addSafety(Difference, OriginKind, std::move(SameOrigin), B->Loc,
                OriginKind != ProofObligationKind::Unsupported ? ""
                : Known ? DifferentObjectsNote
                        : UnknownOriginNote);
      addSafety(Difference, ProofObligationKind::Bounds,
                pointerPositionSafety(B->Lhs.get(), ValidExtents, PointerParams,
                                      OriginExtents, B->Loc),
                B->Loc);
      addSafety(Difference, ProofObligationKind::Bounds,
                pointerPositionSafety(B->Rhs.get(), ValidExtents, PointerParams,
                                      OriginExtents, B->Loc),
                B->Loc);
      // Two null pointers differ by 0 ([expr.add]).
      auto isNull = [&](const VExpr *Ptr) {
        return std::make_unique<VBinOpExpr>(
            VBinOp::Eq, cloneVExpr(Ptr),
            std::make_unique<VLiteralExpr>(0, VType::makePtr(), B->Loc),
            VType::makeBool(), B->Loc);
      };
      auto NotBothNull = makeNot(
          makeAnd(isNull(B->Lhs.get()), isNull(B->Rhs.get()), B->Loc), B->Loc);
      appendGuardedSafety(Out, std::move(Difference), NotBothNull.get(),
                          B->Loc);
    }
    addOperationSafety(E, Out);
    return;
  }
  case VExpr::UnaryOp: {
    const auto *U = static_cast<const VUnaryOpExpr *>(E);
    Collect(U->Operand.get(), Out);
    addOperationSafety(E, Out);
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
    addSafety(
        Out, ProofObligationKind::Initialization,
        initializedSafety(L->Ptr.get(), L->Loc, ObjectModel, OutParameters),
        L->Loc);
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
  case VExpr::Require: {
    const auto *R = static_cast<const VRequireExpr *>(E);
    Collect(R->Cond.get(), Out);
    addSafety(Out, static_cast<ProofObligationKind>(R->ProofKind),
              cloneVExpr(R->Cond.get()), R->Loc);
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
    // Reported at the call, which is what the caller wrote: the helper's
    // operators may lie in another file.
    SafetyChecks Inside;
    Collect(Expanded.get(), Inside);
    for (SafetyCheck &Check : Inside) {
      Check.Cond->Loc = C->Loc;
      Check.Cond->BeginLoc = C->BeginLoc;
      Check.Cond->EndLoc = C->EndLoc;
      Out.push_back(std::move(Check));
    }
    return;
  }
  }
  addSafety(Out, ProofObligationKind::Unsupported, nullptr, E->Loc,
            "an expression whose C++ definedness is not modeled");
}

/// The definedness of the operation \p E itself: what makes its machine
/// value equal its mathematical one, whatever its operands' values.
static std::unique_ptr<VExpr> operationSafety(const VExpr *E) {
  SafetyChecks Checks;
  addOperationSafety(E, Checks);
  std::unique_ptr<VExpr> Safe = makeBoolLiteral(true, E->Loc);
  for (SafetyCheck &Check : Checks)
    Safe = combineSafety(std::move(Safe), std::move(Check.Cond), E->Loc);
  return Safe;
}

static std::unique_ptr<VExpr>
machineMathBridgeForExpr(const VExpr *E, const FunctionMap *FnMap,
                         bool BridgeMachineValue = false) {
  if (!E)
    return makeBoolLiteral(true, SourceLocation());

  switch (E->K) {
  case VExpr::Literal:
    return makeBoolLiteral(true, E->Loc);
  case VExpr::Var:
  case VExpr::Result:
    return keepsEnumRange(E->Ty) ? inEnumRange(E, E->Ty, E->Loc)
                                 : makeBoolLiteral(true, E->Loc);
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
        makeImplies(operationSafety(B), std::move(Equality), B->Loc);
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
        makeImplies(operationSafety(U), std::move(Equality), U->Loc);
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
    auto Bridge = combineSafety(
        machineMathBridgeForExpr(Load->Ptr.get(), FnMap, false),
        machineMathBridgeForExpr(Load->AccessCondition.get(), FnMap, false),
        Load->Loc);
    if (!keepsEnumRange(Load->Ty))
      return Bridge;
    return combineSafety(std::move(Bridge),
                         inEnumRange(Load, Load->Ty, Load->Loc), Load->Loc);
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
  case VExpr::Require:
    return machineMathBridgeForExpr(
        static_cast<const VRequireExpr *>(E)->Cond.get(), FnMap, false);
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
  case VExpr::Require:
    collectDottedVars(static_cast<const VRequireExpr *>(E)->Cond.get(), Out);
    return;
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

static std::unique_ptr<VExpr> substParamsImpl(
    const VExpr *E, const std::map<std::string, std::unique_ptr<VExpr>> &Map,
    const CloneCtx &Ctx, const std::string &EntryHeap,
    const std::string &HeapOverride, std::set<std::string> BoundVars,
    const std::map<std::string, std::unique_ptr<VExpr>> *OldMap,
    const std::set<std::string> *NormalizedPointerChecks);

/// \p E with the actuals of \p Map for its parameters. A node rebuilt from
/// one of \p E keeps the source it spans; an actual keeps its own.
static std::unique_ptr<VExpr> substParams(
    const VExpr *E, const std::map<std::string, std::unique_ptr<VExpr>> &Map,
    const CloneCtx &Ctx, const std::string &EntryHeap,
    const std::string &HeapOverride = "", std::set<std::string> BoundVars = {},
    const std::map<std::string, std::unique_ptr<VExpr>> *OldMap = nullptr,
    const std::set<std::string> *NormalizedPointerChecks = nullptr) {
  auto Result = substParamsImpl(E, Map, Ctx, EntryHeap, HeapOverride,
                                std::move(BoundVars), OldMap,
                                NormalizedPointerChecks);
  if (Result && E && Result->K == E->K && Result->Loc == E->Loc) {
    Result->BeginLoc = E->BeginLoc;
    Result->EndLoc = E->EndLoc;
  }
  return Result;
}

static std::unique_ptr<VExpr> substParamsImpl(
    const VExpr *E, const std::map<std::string, std::unique_ptr<VExpr>> &Map,
    const CloneCtx &Ctx, const std::string &EntryHeap,
    const std::string &HeapOverride, std::set<std::string> BoundVars,
    const std::map<std::string, std::unique_ptr<VExpr>> *OldMap,
    const std::set<std::string> *NormalizedPointerChecks) {
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
  case VExpr::Require: {
    const auto *R = static_cast<const VRequireExpr *>(E);
    return std::make_unique<VRequireExpr>(
        substParams(R->Cond.get(), Map, Ctx, EntryHeap, HeapOverride, BoundVars,
                    OldMap, NormalizedPointerChecks),
        R->ProofKind, R->Loc);
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

/// A structural key of \p C under the quantifiers \p Enclosing, or false.
static bool
applicationKey(const VSpecCallExpr &C,
               const std::vector<const VQuantifiedExpr *> &Enclosing,
               std::string &Key) {
  for (const VQuantifiedExpr *Q : Enclosing) {
    Key += "forall " + Q->Binder;
    if (!Q->Lo)
      Key += " unbounded";
    else if (!expressionKey(Q->Lo.get(), Key) ||
             !expressionKey(Q->Hi.get(), Key))
      return false;
  }
  // Applications in different memory states are different values.
  Key += C.CalleeIdentity + '@' + C.HeapVar;
  for (const auto &Arg : C.Args)
    if (!expressionKey(Arg.get(), Key))
      return false;
  return true;
}

/// Every scalar leaf of a layout at its offset, its array repetitions
/// expanded; nothing when there are more than Limit.
static std::optional<std::vector<std::pair<uint64_t, const VObjectLeaf *>>>
expandedLeaves(const VObjectLayout &Layout, size_t Limit) {
  std::vector<std::pair<uint64_t, const VObjectLeaf *>> Out;
  for (const VObjectLeaf &Leaf : Layout.Leaves) {
    std::vector<uint64_t> Offsets = {Leaf.OffsetBytes};
    for (const VObjectRepeat &Repeat : Leaf.Repeats) {
      std::vector<uint64_t> Next;
      for (uint64_t Start : Offsets)
        for (uint64_t K = 0; K < Repeat.Count; ++K) {
          if (Out.size() + Next.size() >= Limit)
            return std::nullopt;
          Next.push_back(Start + K * Repeat.StrideBytes);
        }
      Offsets = std::move(Next);
    }
    for (uint64_t Offset : Offsets) {
      if (Out.size() >= Limit)
        return std::nullopt;
      Out.push_back({Offset, &Leaf});
    }
  }
  return Out;
}

/// The layout of the object a constructor constructs.
static const VObjectLayout *constructedLayout(const VFunction &Fn) {
  auto Identity = Fn.RecordParams.find("this");
  if (!Fn.IsConstructor || Identity == Fn.RecordParams.end())
    return nullptr;
  auto Layout = llvm::find_if(Fn.Layouts, [&](const VObjectLayout &L) {
    return L.TypeIdentity == Identity->second;
  });
  return Layout == Fn.Layouts.end() ? nullptr : &*Layout;
}

/// The condition a definedness check asks for, without the guards it holds
/// under: `!g || c` as built by makeImplies, and the range of a quantified
/// check.
static const VExpr *checkedCondition(const VExpr *E) {
  while (E) {
    if (E->K == VExpr::BinOp) {
      const auto *B = static_cast<const VBinOpExpr *>(E);
      if (B->Op == VBinOp::Or && B->Lhs->K == VExpr::UnaryOp &&
          static_cast<const VUnaryOpExpr *>(B->Lhs.get())->Op ==
              VUnaryOp::Not) {
        E = B->Rhs.get();
        continue;
      }
    }
    if (E->K == VExpr::Forall) {
      E = static_cast<const VQuantifiedExpr *>(E)->Body.get();
      continue;
    }
    return E;
  }
  return E;
}

/// Whether \p E may have another value at a loop's head than before the
/// loop: it reads a variable, a field, or a heap the loop modifies, outside
/// cppverify::old, which reads the entry state.
static bool readsLoopState(const VExpr *E,
                           const std::set<std::string> &Modified) {
  if (!E)
    return false;
  switch (E->K) {
  case VExpr::Old:
    return false;
  case VExpr::Var: {
    const auto *V = static_cast<const VVarExpr *>(E);
    return Modified.count(V->Name) || Modified.count(V->ProvenanceVariable);
  }
  case VExpr::FieldAccess: {
    const auto *F = static_cast<const VFieldAccessExpr *>(E);
    if (F->Base->K == VExpr::Var) {
      const std::string Prefix =
          static_cast<const VVarExpr *>(F->Base.get())->Name + ".";
      for (const std::string &Name : Modified)
        if (llvm::StringRef(Name).starts_with(Prefix))
          return true;
    }
    break;
  }
  case VExpr::Load:
    if (Modified.count(VHeapName))
      return true;
    break;
  case VExpr::SpecCall:
    if (static_cast<const VSpecCallExpr *>(E)->ReadsHeap &&
        Modified.count(VHeapName))
      return true;
    break;
  case VExpr::UnaryOp: {
    const auto *U = static_cast<const VUnaryOpExpr *>(E);
    if ((U->Op == VUnaryOp::ValidPtr && (Modified.count(VAllocationHeapName) ||
                                         Modified.count(VLivenessHeapName))) ||
        (U->Op == VUnaryOp::InitializedPtr &&
         Modified.count(VInitializationHeapName)))
      return true;
    break;
  }
  default:
    break;
  }
  bool Found = false;
  forEachVExprChild(E, [&](const VExpr *Child) {
    Found = Found || readsLoopState(Child, Modified);
  });
  return Found;
}

/// Whether \p E mentions the variable \p Name free.
static bool mentionsFree(const VExpr *E, const std::string &Name) {
  if (!E)
    return false;
  if (E->K == VExpr::Var)
    return static_cast<const VVarExpr *>(E)->Name == Name;
  if (E->K == VExpr::Forall || E->K == VExpr::Exists) {
    const auto *Q = static_cast<const VQuantifiedExpr *>(E);
    if (Q->Binder == Name)
      return mentionsFree(Q->Lo.get(), Name) || mentionsFree(Q->Hi.get(), Name);
  }
  bool Found = false;
  forEachVExprChild(E, [&](const VExpr *Child) {
    Found = Found || mentionsFree(Child, Name);
  });
  return Found;
}

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
  case VExpr::Require:
    visit(static_cast<const VRequireExpr *>(E)->Cond.get());
    return;
  case VExpr::SpecCall: {
    const auto *C = static_cast<const VSpecCallExpr *>(E);
    for (const auto &Arg : C->Args)
      visit(Arg.get());
    auto It = FnMap.find(C->CalleeIdentity);
    if (It == FnMap.end() || !It->second || !Wanted(*C, *It->second))
      return;
    std::string Key;
    if (applicationKey(*C, Enclosing, Key))
      Out.emplace(std::move(Key), FramedApplication{C, Enclosing});
    return;
  }
  case VExpr::Literal:
  case VExpr::Var:
  case VExpr::Result:
    return;
  }
}

void verify::addChoiceAxioms(std::vector<std::unique_ptr<PassiveStmt>> &Facts,
                             size_t From, const FunctionMap &FnMap,
                             std::set<std::string> &Seen, bool Theorem,
                             ChoiceGuard Guard) {
  auto Chosen = [](const VSpecCallExpr &, const VFunction &Spec) {
    return Spec.IsChoice;
  };
  for (size_t I = From; I < Facts.size(); ++I) {
    std::map<std::string, FramedApplication> Choices;
    std::vector<const VQuantifiedExpr *> Outside;
    collectFramedApplications(Facts[I]->Cond.get(), FnMap, Outside, Choices,
                              Chosen);
    for (const auto &[Found, Application] : Choices) {
      const VSpecCallExpr &Call = *Application.Call;
      // Its axiom holds outside the quantifiers it does not depend on, such
      // as those of an axiom that applies the choice itself.
      std::vector<const VQuantifiedExpr *> Binding;
      for (auto Q = Application.Enclosing.rbegin();
           Q != Application.Enclosing.rend(); ++Q)
        if (mentionsFree(&Call, (*Q)->Binder) ||
            llvm::any_of(Binding, [&](const VQuantifiedExpr *Inner) {
              return mentionsFree(Inner->Lo.get(), (*Q)->Binder) ||
                     mentionsFree(Inner->Hi.get(), (*Q)->Binder);
            }))
          Binding.insert(Binding.begin(), *Q);
      std::string Key;
      if (!applicationKey(Call, Binding, Key) || !Seen.insert(Key).second)
        continue;
      const VFunction &Choice = *FnMap.at(Call.CalleeIdentity);
      std::unique_ptr<VExpr> Fact =
          specApplicationFacts(Choice, Call.Args, &Call, Call.Loc,
                               Call.ReadsHeap ? Call.HeapVar : std::string());
      if (Fact && Guard)
        Fact = Guard(std::move(Fact), Choice, Call);
      if (!Fact)
        continue;
      for (auto Q = Binding.rbegin(); Q != Binding.rend(); ++Q)
        Fact = std::make_unique<VForallExpr>(
            (*Q)->Binder, cloneVExpr((*Q)->Lo.get()),
            cloneVExpr((*Q)->Hi.get()), std::move(Fact), Call.Loc,
            (*Q)->BinderType);
      auto Instance = std::make_unique<PassiveStmt>();
      Instance->K = PassiveStmt::Assume;
      Instance->Theorem = Theorem;
      Instance->Origin = "choose";
      Instance->Cond = std::move(Fact);
      Facts.push_back(std::move(Instance));
    }
  }
}

/// A store outside the reads ranges of a spec leaves its value unchanged, and
/// a step that keeps every value a choice's condition reads keeps the choice.
/// For each application, relate it across every store back from its heap
/// state.
static void addFrameInstances(PassiveProgram &P, const FunctionMap &FnMap) {
  auto Framed = [](const VSpecCallExpr &Call, const VFunction &Spec) {
    return Call.ReadsHeap && !Call.HeapVar.empty() &&
           (!Spec.Reads.empty() || Spec.IsChoice);
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
      if (Spec.IsChoice) {
        Outside = choiceReadsAgree(Spec, *Call, S.Before, S.After, FnMap, Loc);
      } else if (S.Address) {
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
      Instance->Theorem = true;
      Instance->Origin = "reads:" + Spec.Name;
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

PassiveOversize verify::specFactsOversize(const NodeBudget &Budget) {
  return {"the facts about the specs it applies (at each application, their "
          "definitions unfolded as deep as their fuel, and their "
          "postconditions)",
          Budget.built(), Budget.limit(),
          "lower the fuel cppverify::reveal_with_fuel gives, or raise the "
          "limit"};
}

/// A spec's proved postcondition, and an inductive predicate's unfolding,
/// hold at every application of it. An inductive predicate is unfolded
/// \p Depth levels deep, or as deep as reveal_with_fuel asks when \p WithFuel:
/// the applications inside an unfolding are unfolded in turn.
static void
addSpecPostInstances(PassiveProgram &P, const FunctionMap &FnMap,
                     const VFunction &Fn, unsigned Depth, bool WithFuel,
                     const std::vector<std::unique_ptr<VExpr>> &EntryMeasure) {
  const std::set<std::string> &Withheld = Fn.FactsWithheld;
  auto depthOf = [&](const VFunction &Spec) {
    auto It = Fn.SpecFuel.find(Spec.Identity);
    return !WithFuel || It == Fn.SpecFuel.end() ? Depth
                                                : std::max(Depth, It->second);
  };
  auto WithPost = [&](const VSpecCallExpr &, const VFunction &Spec) {
    return (!Spec.Postconditions.empty() || Spec.Unfolding) &&
           !Withheld.count(Spec.Identity) && !Fn.Cluster.count(Spec.Identity);
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
  std::set<std::string> Seen;
  std::vector<const VExpr *> Unfolded;
  auto addFacts = [&](const std::map<std::string, FramedApplication> &Found) {
    for (const auto &[Key, Application] : Found) {
      if (!Seen.insert(Key).second)
        continue;
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
            (*Q)->Binder, cloneVExpr((*Q)->Lo.get()),
            cloneVExpr((*Q)->Hi.get()), std::move(Fact), Call.Loc,
            (*Q)->BinderType);
      auto Instance = std::make_unique<PassiveStmt>();
      Instance->K = PassiveStmt::Assume;
      Instance->Theorem = true;
      Instance->Origin = "spec:" + Spec.Name;
      Instance->Cond = std::move(Fact);
      if (Spec.Unfolding)
        Unfolded.push_back(Instance->Cond.get());
      Facts.push_back(std::move(Instance));
    }
  };
  // The applications inside the definitions the solver receives, as
  // Dafny's function postconditions hold at every application.
  auto Defined = [&](const VSpecCallExpr &, const VFunction &Spec) {
    return !Withheld.count(Spec.Identity);
  };
  std::map<std::string, FramedApplication> Named;
  for (const auto &Assumption : P.EntryAssumes)
    collectFramedApplications(Assumption.get(), FnMap, Enclosing, Named,
                              Defined);
  for (const auto &S : P.Stmts)
    collectFramedApplications(S->Cond.get(), FnMap, Enclosing, Named, Defined);
  for (const auto &Exit : P.ExitAsserts)
    collectFramedApplications(Exit.Cond.get(), FnMap, Enclosing, Named,
                              Defined);
  std::vector<std::unique_ptr<VExpr>> Levels;
  for (const auto &[Key, Application] : Named) {
    for (auto &Level :
         specDefinitionLevels(*Application.Call, FnMap, P.SpecFuel,
                              P.HiddenSpecs, P.RevealedSpecs)) {
      std::vector<const VQuantifiedExpr *> Outer = Application.Enclosing;
      collectFramedApplications(Level.get(), FnMap, Outer, Applications,
                                WithPost);
      Levels.push_back(std::move(Level));
    }
  }
  addFacts(Applications);
  for (unsigned Level = 2; !Unfolded.empty(); ++Level) {
    auto Deeper = [&](const VSpecCallExpr &, const VFunction &Spec) {
      return Spec.Unfolding && !Withheld.count(Spec.Identity) &&
             depthOf(Spec) >= Level;
    };
    std::map<std::string, FramedApplication> Next;
    for (const VExpr *Fact : Unfolded)
      collectFramedApplications(Fact, FnMap, Enclosing, Next, Deeper);
    Unfolded.clear();
    addFacts(Next);
  }
  // The specs of the function's cluster, where their measure is below the
  // function's at entry: the induction hypothesis of their joint proof.
  auto InCluster = [&](const VSpecCallExpr &, const VFunction &Spec) {
    return Fn.Cluster.count(Spec.Identity) && !Withheld.count(Spec.Identity);
  };
  std::map<std::string, FramedApplication> Members;
  if (!EntryMeasure.empty()) {
    for (const auto &Assumption : P.EntryAssumes)
      collectFramedApplications(Assumption.get(), FnMap, Enclosing, Members,
                                InCluster);
    for (const auto &S : P.Stmts)
      collectFramedApplications(S->Cond.get(), FnMap, Enclosing, Members,
                                InCluster);
    for (const auto &Exit : P.ExitAsserts)
      collectFramedApplications(Exit.Cond.get(), FnMap, Enclosing, Members,
                                InCluster);
  }
  for (const auto &[Key, Application] : Members) {
    const VSpecCallExpr &Call = *Application.Call;
    const VFunction &Spec = *FnMap.at(Call.CalleeIdentity);
    std::unique_ptr<VExpr> Fact = specInductionFacts(
        Spec, Call.Args, &Call, Call.Loc, EntryMeasure, FnMap,
        Call.ReadsHeap ? Call.HeapVar : std::string());
    if (!Fact)
      continue;
    if (!Spec.Postconditions.empty())
      P.InductivePosts.insert(Spec.Identity);
    for (auto Q = Application.Enclosing.rbegin();
         Q != Application.Enclosing.rend(); ++Q)
      Fact = std::make_unique<VForallExpr>(
          (*Q)->Binder, cloneVExpr((*Q)->Lo.get()), cloneVExpr((*Q)->Hi.get()),
          std::move(Fact), Call.Loc, (*Q)->BinderType);
    auto Instance = std::make_unique<PassiveStmt>();
    Instance->K = PassiveStmt::Assume;
    Instance->Origin = "spec:" + Spec.Name;
    Instance->Cond = std::move(Fact);
    Facts.push_back(std::move(Instance));
  }
  addChoiceAxioms(Facts, 0, FnMap, Seen, true);
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
  /// The value heap at entry.
  std::string EntryHeapVersion;
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
  /// Where the assumptions being emitted come from (PassiveStmt::Origin).
  std::string Origin;
  std::vector<std::unique_ptr<VExpr>> ReturnGuards;
  std::vector<std::string> OwnedAllocationIdentities;
  std::map<std::string, std::unique_ptr<VExpr>> ReferenceBindings;
  std::set<std::string> PointerValueVariables;
  std::set<std::string> ProvenanceVariables;
  std::vector<VValidExtent> ActiveValidExtents;
  std::set<std::string> PointerParameterNames;
  std::set<std::string> SourcePointerParameterNames;
  /// The entry versions of the out-parameters, which are never reassigned:
  /// a renamed address based on one is in storage whose initialization the
  /// function tracks.
  std::set<std::string> OutParameterVersions;
  /// The objects of the pointer parameters, for origins: the declared
  /// extents, and one object of its pointee type (no length) for a
  /// parameter without one.
  std::vector<VValidExtent> OriginObjects;
  std::set<std::string> RepresentedAllocationPointers;
  /// The type and size of the object each of those pointers was defined to
  /// address.
  std::map<std::string, std::pair<VType, uint64_t>> RepresentedObjects;
  std::vector<StoredPointerCell> StoredPointerCells;
  std::set<std::string> HeapBases;
  std::set<std::string> HeapVariables;
  std::map<std::string, PassiveModelVariable> ModelVariables;
  /// The path condition of the statement being passivized, for the versions
  /// it defines.
  const std::unique_ptr<VExpr> *VersionGuard = nullptr;
  std::map<std::string, std::set<std::string>> SourceVersions;
  std::set<std::string> SuppressedSourceVariables;
  std::vector<PassiveTraceEvent> TraceEvents;
  std::string ResultVar = "__result";
  const VFunction &Fn;
  FunctionMap FnMap;
  unsigned UnfoldingDepth = 1;
  bool UnfoldingFuel = true;
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
      // A region of one scalar object is one cell.
      if (InnerIsRegion && InnerBytes && InnerBytes->Cell)
        return makeEq(cloneVExpr(OuterPtr), cloneVExpr(InnerBytes->Lo.get()),
                      Loc);
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

  /// In the object model a slice argument is valid storage where its bytes
  /// [Actual, Actual + Bytes] lie in one of the caller's objects: those its
  /// origins name when they are known, else any of them. Arg is the
  /// argument as written, which carries the origins.
  std::unique_ptr<VExpr> objectContainment(
      const VExpr *Arg, const VExpr *Actual, std::unique_ptr<VExpr> Bytes,
      const std::map<std::string, std::string> &Renames, SourceLocation Loc) {
    std::vector<Region> Objects;
    auto Origins = pointerOrigins(Arg);
    if (Origins && !Origins->empty() && !hasPointerProvenance(Arg)) {
      for (const std::string &Origin : *Origins) {
        if (isGlobalOrigin(Origin)) {
          auto [Address, Size] = globalOriginExtent(Origin);
          auto Start =
              std::make_unique<VLiteralExpr>(Address, VType::makePtr(), Loc);
          auto End =
              addBytes(cloneVExpr(Start.get()),
                       std::make_unique<VLiteralExpr>(std::to_string(Size),
                                                      pointerOffsetType(), Loc),
                       Loc);
          Objects.push_back(Region{std::move(Start), std::move(End)});
        } else if (auto Object = entryObjectRegion(Origin, Renames, Loc)) {
          Objects.push_back(std::move(*Object));
        }
      }
    } else if (!hasPointerProvenance(Arg)) {
      for (const AbstractObject &Object : abstractObjects(Fn))
        if (auto Region = entryObjectRegion(Object.Name, Renames, Loc))
          Objects.push_back(std::move(*Region));
    }
    auto End = addBytes(cloneVExpr(Actual), std::move(Bytes), Loc);
    std::unique_ptr<VExpr> Any = makeBoolLiteral(false, Loc);
    for (Region &Object : Objects)
      Any = makeOr(std::move(Any),
                   makeAnd(std::make_unique<VBinOpExpr>(
                               VBinOp::Le, std::move(Object.Lo),
                               cloneVExpr(Actual), VType::makeBool(), Loc),
                           std::make_unique<VBinOpExpr>(
                               VBinOp::Le, cloneVExpr(End.get()),
                               std::move(Object.Hi), VType::makeBool(), Loc),
                           Loc),
                   Loc);
    return Any;
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
      if (isRegionFootprint(F, Fn.ScalarReferenceParams)) {
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
      if (isRegionFootprint(M, Fn.ScalarReferenceParams)) {
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

  /// The one cell a store through \p Address writes, when the address is a
  /// pointer into local or dynamic storage (a reference to a local, say) that
  /// the loop assigns neither nor its lifetime companion.
  std::optional<Region>
  representedCell(const VExpr *Address, const VType &CellType,
                  const std::map<std::string, std::string> &Renames,
                  const std::set<std::string> &Assigned, SourceLocation Loc) {
    while (Address && Address->K == VExpr::Cast)
      Address = static_cast<const VCastExpr *>(Address)->Inner.get();
    if (!Address || Address->K != VExpr::Var)
      return std::nullopt;
    const auto *Pointer = static_cast<const VVarExpr *>(Address);
    if (Pointer->ProvenanceVariable.empty() || Assigned.count(Pointer->Name) ||
        Assigned.count(Pointer->ProvenanceVariable))
      return std::nullopt;
    CloneCtx Ctx{Renames, OldState, false};
    auto Cell = cloneExpr(Address, Ctx);
    return cellRegion(Cell.get(), CellType, Loc);
  }

  /// The local or dynamic object that the pointer its allocation defined
  /// addresses, when the loop assigns neither the pointer nor its lifetime
  /// companion: every access through it lies in the object, at a field of
  /// its layout and an index its fixed array bounds (a dynamic object is one
  /// scalar). The object is its scalar leaves, each one cell, so the loop's
  /// frame stays a chain of stores; without a layout it is its bytes.
  bool representedRegions(const VExpr *Root,
                          const std::map<std::string, std::string> &Renames,
                          const std::set<std::string> &Assigned,
                          SourceLocation Loc, std::vector<Region> &Out) {
    if (!Root || Root->K != VExpr::Var)
      return false;
    const auto *Pointer = static_cast<const VVarExpr *>(Root);
    auto Object = RepresentedObjects.find(Pointer->Name);
    if (Object == RepresentedObjects.end() ||
        Pointer->ProvenanceVariable.empty() || Assigned.count(Pointer->Name) ||
        Assigned.count(Pointer->ProvenanceVariable))
      return false;
    const auto &[Type, Bytes] = Object->second;
    CloneCtx Ctx{Renames, OldState, false};
    auto Base = cloneExpr(Root, Ctx);
    auto At = [&](uint64_t Offset) {
      return addBytes(cloneVExpr(Base.get()),
                      std::make_unique<VLiteralExpr>(std::to_string(Offset),
                                                     pointerOffsetType(), Loc),
                      Loc);
    };
    if (Type.isInt() || Type.Kind == VTypeKind::Bool ||
        Type.Kind == VTypeKind::Ptr) {
      Out.push_back(cellRegion(Base.get(), Type, Loc));
      return true;
    }
    const auto Layout = llvm::find_if(Fn.Layouts, [&](const VObjectLayout &L) {
      return L.TypeIdentity == Type.TypeIdentity;
    });
    if (Layout != Fn.Layouts.end() && Layout->SizeBytes == Bytes)
      if (auto Leaves = expandedLeaves(*Layout, Bytes);
          Leaves && !Leaves->empty()) {
        for (const auto &[Offset, Leaf] : *Leaves)
          Out.push_back(cellRegion(At(Offset).get(), Leaf->Ty, Loc));
        return true;
      }
    Out.push_back(
        Region{cloneVExpr(Base.get()), At(std::max<uint64_t>(Bytes, 1))});
    return true;
  }

  bool loopWriteRegions(const std::vector<std::unique_ptr<VStmt>> &Stmts,
                        const std::map<std::string, std::string> &Renames,
                        const std::set<std::string> &Assigned,
                        std::vector<Region> &Out) {
    for (const auto &S : Stmts) {
      switch (S->K) {
      case VStmt::Store: {
        const auto &St = static_cast<const VStoreStmt &>(*S);
        auto R = parameterCell(St.Ptr.get(), St.Value->Ty, Renames, St.Loc);
        if (!R)
          R = representedCell(St.Ptr.get(), St.Value->Ty, Renames, Assigned,
                              St.Loc);
        if (!R &&
            originRegions(addressRoot(St.Ptr.get()), Renames, St.Loc, Out))
          break;
        if (!R)
          R = rootRegion(addressRoot(St.Ptr.get()), Renames, St.Loc);
        if (!R && representedRegions(addressRoot(St.Ptr.get()), Renames,
                                     Assigned, St.Loc, Out))
          break;
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
              (!isRegionFootprint(M, Callee->ScalarReferenceParams) ||
               (Callee->ObjectModel &&
                (Target->Ty.isInt() || Target->Ty.Kind == VTypeKind::Bool ||
                 Target->Ty.Kind == VTypeKind::Ptr) &&
                llvm::none_of(Callee->ValidExtents,
                              [&](const VValidExtent &Extent) {
                                return Extent.Base == Param;
                              })));
          if (OneCell) {
            auto Cell = parameterCell(Actual, Target->Ty, Renames, C.Loc);
            if (!Cell)
              Cell =
                  representedCell(Actual, Target->Ty, Renames, Assigned, C.Loc);
            if (Cell) {
              Out.push_back(std::move(*Cell));
              continue;
            }
          }
          if (originRegions(addressRoot(Actual), Renames, C.Loc, Out))
            continue;
          auto R = rootRegion(addressRoot(Actual), Renames, C.Loc);
          if (!R && representedRegions(addressRoot(Actual), Renames, Assigned,
                                       C.Loc, Out))
            continue;
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
        if (!loopWriteRegions(I.Then, Renames, Assigned, Out) ||
            !loopWriteRegions(I.Else, Renames, Assigned, Out))
          return false;
        break;
      }
      case VStmt::While:
        if (!loopWriteRegions(static_cast<const VWhileStmt &>(*S).Body, Renames,
                              Assigned, Out))
          return false;
        break;
      case VStmt::Seq:
        if (!loopWriteRegions(static_cast<const VSeqStmt &>(*S).Stmts, Renames,
                              Assigned, Out))
          return false;
        break;
      default:
        break;
      }
    }
    return true;
  }

  /// Whether two offsets are the same term, by structure.
  static bool sameOffset(const VExpr *A, const VExpr *B) {
    if (!A || !B || A->K != B->K)
      return false;
    switch (A->K) {
    case VExpr::Literal:
      return static_cast<const VLiteralExpr *>(A)->Value ==
             static_cast<const VLiteralExpr *>(B)->Value;
    case VExpr::Var:
      return static_cast<const VVarExpr *>(A)->Name ==
             static_cast<const VVarExpr *>(B)->Name;
    case VExpr::Cast:
      return sameRepresentation(A->Ty, B->Ty) &&
             sameOffset(static_cast<const VCastExpr *>(A)->Inner.get(),
                        static_cast<const VCastExpr *>(B)->Inner.get());
    case VExpr::BinOp: {
      const auto *L = static_cast<const VBinOpExpr *>(A);
      const auto *R = static_cast<const VBinOpExpr *>(B);
      return L->Op == R->Op && sameOffset(L->Lhs.get(), R->Lhs.get()) &&
             sameOffset(L->Rhs.get(), R->Rhs.get());
    }
    default:
      return false;
    }
  }

  /// How a quantifier's loads use its binder j: the distinct element offsets
  /// c of the slice actuals `base + S*c` it indexes as `(base + S*c) + S*j`,
  /// whether one is indexed directly (`base + S*j`), and whether one uses j
  /// otherwise.
  struct SliceUse {
    std::vector<const VExpr *> Offsets;
    bool Direct = false;
    bool Other = false;
  };

  static void collectSliceOffsets(const VExpr *E, const std::string &Binder,
                                  SliceUse &Use) {
    if (!E || Use.Other)
      return;
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
      if (mentionsFree(Address, Binder)) {
        const auto *Outer = Address->K == VExpr::BinOp
                                ? static_cast<const VBinOpExpr *>(Address)
                                : nullptr;
        uint64_t IndexStride = 0, OffsetStride = 0;
        const VExpr *Index = Outer && Outer->Op == VBinOp::Add
                                 ? scaled(Outer->Rhs.get(), IndexStride)
                                 : nullptr;
        if (!Index || Outer->Lhs->Ty.Kind != VTypeKind::Ptr ||
            Index->K != VExpr::Var ||
            static_cast<const VVarExpr *>(Index)->Name != Binder ||
            mentionsFree(Outer->Lhs.get(), Binder)) {
          Use.Other = true;
          return;
        }
        const auto *Inner =
            Outer->Lhs->K == VExpr::BinOp
                ? static_cast<const VBinOpExpr *>(Outer->Lhs.get())
                : nullptr;
        const VExpr *Offset = Inner && Inner->Op == VBinOp::Add &&
                                      Inner->Lhs->Ty.Kind == VTypeKind::Ptr
                                  ? scaled(Inner->Rhs.get(), OffsetStride)
                                  : nullptr;
        if (Offset && OffsetStride == IndexStride && Offset->Ty.isInt()) {
          if (llvm::none_of(Use.Offsets, [&](const VExpr *Seen) {
                return sameOffset(Seen, Offset);
              }))
            Use.Offsets.push_back(Offset);
        } else {
          Use.Direct = true;
        }
      }
    }
    auto visit = [&](const VExpr *Child) {
      collectSliceOffsets(Child, Binder, Use);
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
  }

  /// \p Q restated over the indices of a slice's base: j := k - c, a change
  /// of variables.
  std::unique_ptr<VExpr> rebased(const VQuantifiedExpr &Q, const VExpr *Offset,
                                 const std::string &Name) {
    const SourceLocation Loc = Q.Loc;
    const VType MathTy = Q.BinderType;
    auto mathOf = [&](const VExpr *V) -> std::unique_ptr<VExpr> {
      if (V->Ty.IntMode == VIntMode::Math)
        return cloneVExpr(V);
      VType To = V->Ty;
      To.IntMode = VIntMode::Math;
      return std::make_unique<VCastExpr>(cloneVExpr(V), V->Ty, To, Loc);
    };
    std::map<std::string, std::unique_ptr<VExpr>> Shift;
    Shift[Q.Binder] = std::make_unique<VBinOpExpr>(
        VBinOp::Sub, std::make_unique<VVarExpr>(Name, MathTy, Loc),
        mathOf(Offset), MathTy, Loc);
    auto Body = substParamsInExpr(Q.Body.get(), Shift);
    if (!Body)
      return nullptr;
    // Over all integers the shift changes no range.
    std::unique_ptr<VExpr> Lo, Hi;
    if (Q.Lo) {
      Lo = std::make_unique<VBinOpExpr>(VBinOp::Add, mathOf(Q.Lo.get()),
                                        mathOf(Offset), MathTy, Loc);
      Hi = std::make_unique<VBinOpExpr>(VBinOp::Add, mathOf(Q.Hi.get()),
                                        mathOf(Offset), MathTy, Loc);
    }
    if (Q.K == VExpr::Forall)
      return std::make_unique<VForallExpr>(Name, std::move(Lo), std::move(Hi),
                                           std::move(Body), Loc, MathTy);
    return std::make_unique<VExistsExpr>(Name, std::move(Lo), std::move(Hi),
                                         std::move(Body), Loc, MathTy);
  }

  /// A contract quantifier that indexes a slice actual `base + c` from zero
  /// is restated over base's indices, j := k - c, so that the caller's own
  /// terms trigger its instantiation. With loads through slices at several
  /// offsets, or directly, no one change of variables suits them all: an
  /// assumption (\p Assumed) then keeps the quantifier and adds its
  /// restatement over each slice's base, which are equivalent, each with the
  /// triggers of its own form; a check is left as it is.
  std::unique_ptr<VExpr> rebaseSliceBinders(std::unique_ptr<VExpr> E,
                                            bool Assumed) {
    if (!E)
      return E;
    switch (E->K) {
    case VExpr::BinOp: {
      auto *B = static_cast<VBinOpExpr *>(E.get());
      B->Lhs = rebaseSliceBinders(std::move(B->Lhs), Assumed);
      B->Rhs = rebaseSliceBinders(std::move(B->Rhs), Assumed);
      return E;
    }
    case VExpr::UnaryOp: {
      auto *U = static_cast<VUnaryOpExpr *>(E.get());
      U->Operand = rebaseSliceBinders(std::move(U->Operand), Assumed);
      return E;
    }
    case VExpr::Cast: {
      auto *C = static_cast<VCastExpr *>(E.get());
      C->Inner = rebaseSliceBinders(std::move(C->Inner), Assumed);
      return E;
    }
    case VExpr::Conditional: {
      auto *C = static_cast<VConditionalExpr *>(E.get());
      C->Cond = rebaseSliceBinders(std::move(C->Cond), Assumed);
      C->Then = rebaseSliceBinders(std::move(C->Then), Assumed);
      C->Else = rebaseSliceBinders(std::move(C->Else), Assumed);
      return E;
    }
    case VExpr::Forall:
    case VExpr::Exists: {
      auto *Q = static_cast<VQuantifiedExpr *>(E.get());
      Q->Body = rebaseSliceBinders(std::move(Q->Body), Assumed);
      if (Q->BinderType.IntMode != VIntMode::Math)
        return E;
      SliceUse Use;
      collectSliceOffsets(Q->Body.get(), Q->Binder, Use);
      if (Use.Other || Use.Offsets.empty())
        return E;
      if (Use.Offsets.size() == 1 && !Use.Direct) {
        auto Restated =
            rebased(*Q, Use.Offsets.front(), Q->Binder + "_rebased");
        return Restated ? std::move(Restated) : std::move(E);
      }
      if (!Assumed)
        return E;
      std::unique_ptr<VExpr> All = std::move(E);
      const auto &Original = static_cast<const VQuantifiedExpr &>(*All);
      std::vector<std::unique_ptr<VExpr>> Restatements;
      for (size_t I = 0; I != Use.Offsets.size(); ++I)
        if (auto Restated =
                rebased(Original, Use.Offsets[I],
                        Original.Binder + "_rebased" +
                            (I ? std::to_string(I + 1) : std::string())))
          Restatements.push_back(std::move(Restated));
      const SourceLocation Loc = All->Loc;
      for (auto &Restated : Restatements)
        All = std::make_unique<VBinOpExpr>(VBinOp::And, std::move(All),
                                           std::move(Restated),
                                           VType::makeBool(), Loc);
      return All;
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
    std::shared_ptr<const VExpr> Guard;
    if (VersionGuard && *VersionGuard)
      Guard = cloneVExpr(VersionGuard->get());
    ModelVariables[Versioned] = {
        Source->second.DisplayName, Source->second.Type,
        Source->second.Loc,         Source->second.EndLoc,
        Source->second.Reference,   std::move(Guard)};
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
    if (K == PassiveStmt::Assume)
      PS->Origin = Origin;
    PS->TraceEventCount = TraceEvents.size();
    if (K == PassiveStmt::Assert && Cond)
      PS->Focus = {Cond->Loc, Cond->BeginLoc, Cond->EndLoc};
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
    case ProofObligationKind::BuiltinArgument:
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
    llvm::SaveAndRestore<std::string> Kept(Origin, "keep");
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
    llvm::SaveAndRestore<std::string> Returned(Origin, "ret");
    emitMathBridge(P, Result.get(), nullptr, SourceLocation(), true);
    emitPassive(P, PassiveStmt::Assume,
                makeEq(std::make_unique<VVarExpr>(ResultName, Fn.ReturnType,
                                                  SourceLocation()),
                       std::move(Result), SourceLocation()));
    P.ResultVarName = ResultName;
  }

  /// Whether S starts a lifetime, whose storage is then uninitialized.
  static bool startsLifetime(const VStmt &S) {
    switch (S.K) {
    case VStmt::Allocate:
      return true;
    case VStmt::If: {
      const auto &I = static_cast<const VIfStmt &>(S);
      return llvm::any_of(I.Then,
                          [](const auto &T) { return startsLifetime(*T); }) ||
             llvm::any_of(I.Else,
                          [](const auto &E) { return startsLifetime(*E); });
    }
    case VStmt::While:
      return llvm::any_of(static_cast<const VWhileStmt &>(S).Body,
                          [](const auto &B) { return startsLifetime(*B); });
    case VStmt::GhostBlock:
      return llvm::any_of(static_cast<const VGhostBlockStmt &>(S).Body,
                          [](const auto &B) { return startsLifetime(*B); });
    case VStmt::Seq:
      return llvm::any_of(static_cast<const VSeqStmt &>(S).Stmts,
                          [](const auto &B) { return startsLifetime(*B); });
    default:
      return false;
    }
  }

  /// `forall a. initialized_before[a] -> initialized_after[a]`, triggered by
  /// reads of the later state.
  static std::unique_ptr<VExpr> initializationKept(const std::string &Before,
                                                   const std::string &After,
                                                   SourceLocation Loc) {
    const std::string Binder = "__init_address";
    auto Address = [&] {
      return std::make_unique<VBinOpExpr>(
          VBinOp::Add, std::make_unique<VLiteralExpr>(0, VType::makePtr(), Loc),
          std::make_unique<VVarExpr>(Binder, VType::makeInt32(VIntMode::Math),
                                     Loc),
          VType::makePtr(), Loc);
    };
    auto WasInitialized =
        std::make_unique<VLoadExpr>(Address(), VType::makeBool(), Loc, Before);
    auto IsInitialized = std::make_unique<VCastExpr>(
        std::make_unique<VLoadExpr>(Address(), VType::makeBool(), Loc, After),
        VType::makeBool(), VType::makeBool(), Loc, /*IsTrigger=*/true);
    return std::make_unique<VForallExpr>(
        Binder, nullptr, nullptr,
        makeOr(makeNot(std::move(WasInitialized), Loc),
               std::move(IsInitialized), Loc),
        Loc, VType::makeInt32(VIntMode::Math));
  }

  /// Whether the function tracks the initialization of the storage Ptr
  /// addresses, source or renamed: local or dynamic storage, or an
  /// out-parameter's.
  bool tracksInitialization(const VExpr *Ptr) const {
    if (hasPointerProvenance(Ptr))
      return true;
    const VExpr *Base = pointerBase(Ptr);
    if (!Base || Base->K != VExpr::Var)
      return false;
    const std::string &Name = static_cast<const VVarExpr *>(Base)->Name;
    return Fn.OutParameters.count(Name) || OutParameterVersions.count(Name);
  }

  void collectModified(const VStmt &S, std::set<std::string> &Out) const {
    switch (S.K) {
    case VStmt::Assign:
      Out.insert(static_cast<const VAssignStmt &>(S).Target);
      break;
    case VStmt::Store:
      Out.insert(VHeapName);
      // A store to storage whose initialization is tracked initializes the
      // cell.
      if (tracksInitialization(static_cast<const VStoreStmt &>(S).Ptr.get()))
        Out.insert(VInitializationHeapName);
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
      if (Callee != FnMap.end())
        for (unsigned I = 0;
             I < C.Args.size() && I < Callee->second->Params.size(); ++I)
          if (Callee->second->OutParameters.count(
                  Callee->second->Params[I].first) &&
              tracksInitialization(C.Args[I].get()))
            Out.insert(VInitializationHeapName);
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

  /// The memory checks of invariant Inv of W, as memory checking recorded
  /// them.
  static const std::vector<VMemoryCheck> *invariantChecks(const VWhileStmt &W,
                                                          const VExpr *Inv) {
    for (size_t I = 0;
         I != W.Invariants.size() && I != W.InvariantChecks.size(); ++I)
      if (W.Invariants[I].get() == Inv)
        return &W.InvariantChecks[I];
    return nullptr;
  }

  /// A contract expression's memory checks, recorded before spec inlining,
  /// join its other checks, one obligation per kind.
  /// The definedness checks of E, or of SafetySource, the clause as written
  /// that E instantiates, with the memory checks recorded for it.
  SafetyChecks exprSafetyChecks(const VExpr *E, const VExpr *SafetySource,
                                const std::vector<VMemoryCheck> *MemoryChecks) {
    SafetyChecks Checks;
    collectSafety(
        SafetySource ? SafetySource : E, &FnMap,
        SafetySource ? &Fn.ValidExtents : &ActiveValidExtents,
        SafetySource ? &SourcePointerParameterNames : &PointerParameterNames,
        Checks, Fn.ObjectModel, SafetySource ? &OriginObjects : nullptr,
        SafetySource ? &Fn.OutParameters : &OutParameterVersions);
    if (MemoryChecks && !Fn.TotalExpressions)
      for (const VMemoryCheck &Check : *MemoryChecks)
        Checks.push_back({Check.Kind, cloneVExpr(Check.Cond.get())});
    return Checks;
  }

  void emitExprSafety(PassiveProgram &P, const VExpr *E, const VExpr *Guard,
                      SourceLocation Loc,
                      const std::map<std::string, std::string> &Renames,
                      bool BridgeMachineValue = false,
                      const VExpr *SafetySource = nullptr,
                      const std::vector<VMemoryCheck> *MemoryChecks = nullptr) {
    SafetyChecks Checks = exprSafetyChecks(E, SafetySource, MemoryChecks);
    groupByKind(Checks);
    CloneCtx Ctx{Renames, OldState, false};
    for (const SafetyCheck &Check : Checks)
      emitPassive(P, PassiveStmt::Assert, cloneExpr(Check.Cond.get(), Ctx),
                  Guard, Loc, Check.Kind, Check.Note);
    emitMathBridge(P, E, Guard, Loc, BridgeMachineValue);
  }

  /// The definedness of an invariant, assumed at its loop's head: every
  /// path into the head (entry, the end of an iteration, a continue) asserts
  /// it with the invariant, so at the head it holds by the same induction,
  /// and the reads it makes, of memory written in the loop included, are
  /// initialized and in bounds there. A check whose condition reads nothing
  /// the loop modifies is left out: what it asks for holds at the head as it
  /// did before the loop, and its guards alone, of state the loop changes,
  /// are what an invariant states itself.
  void assumeInvariantSafety(PassiveProgram &P, const VWhileStmt &W,
                             const VExpr *Inv, const VExpr *Guard,
                             const std::map<std::string, std::string> &Renames,
                             const std::set<std::string> &Modified) {
    CloneCtx Ctx{Renames, OldState, false};
    for (const SafetyCheck &Check :
         exprSafetyChecks(Inv, Inv, invariantChecks(W, Inv)))
      if (readsLoopState(checkedCondition(Check.Cond.get()), Modified))
        emitPassive(P, PassiveStmt::Assume, cloneExpr(Check.Cond.get(), Ctx),
                    Guard, Inv->Loc);
  }

  void emitMathBridge(PassiveProgram &P, const VExpr *E, const VExpr *Guard,
                      SourceLocation Loc, bool BridgeMachineValue = false) {
    llvm::SaveAndRestore<std::string> Exact(Origin, "exact");
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
    RepresentedObjects[ResultTarget.str()] = {Summary.AllocatedType,
                                              Summary.SizeBytes};
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
  PassivizerImpl(const VFunction &Fn, FunctionMap FnMap,
                 unsigned UnfoldingDepth, bool UnfoldingFuel)
      : Fn(Fn), FnMap(std::move(FnMap)), UnfoldingDepth(UnfoldingDepth),
        UnfoldingFuel(UnfoldingFuel) {}

  /// The entry state: the parameters and heaps at their first versions, and
  /// the facts that hold there, among them the preconditions (only the
  /// generated ones unless WrittenPreconditions).
  std::map<std::string, std::string> enter(PassiveProgram &P,
                                           bool WrittenPreconditions) {
    AssignedNames = assignedNames(Fn.Body);

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
    EntryHeapVersion = versionedName(VHeapName);

    std::map<std::string, std::string> Renames;
    for (const char *Heap : StateHeaps) {
      std::string Heap0Name = versionedName(Heap);
      OldState[Heap] = std::make_unique<VVarExpr>(Heap0Name, VType::makePtr(),
                                                  SourceLocation());
      Renames[Heap] = Heap0Name;
    }

    for (const auto &Param : Fn.Params) {
      std::string V0 = versionedName(Param.first);
      OldState[Param.first] = std::make_unique<VVarExpr>(
          V0, Param.second, SourceLocation(),
          Fn.IsConstructor && Param.first == "this" ? VConstructedObjectLifetime
                                                    : "");
      Renames[Param.first] = V0;
      if (Param.second.Kind == VTypeKind::Ptr) {
        PointerParameterNames.insert(V0);
        SourcePointerParameterNames.insert(Param.first);
      }
      if (Fn.OutParameters.count(Param.first))
        OutParameterVersions.insert(V0);
    }
    for (const VValidExtent &Extent : Fn.ValidExtents)
      OriginObjects.emplace_back(Extent.Base, Extent.PointerType,
                                 cloneVExpr(Extent.Length.get()));
    for (const auto &[Name, Ty] : Fn.Params)
      if (Ty.Kind == VTypeKind::Ptr &&
          llvm::none_of(Fn.ValidExtents, [&, &Name = Name](const auto &E) {
            return E.Base == Name;
          }))
        OriginObjects.emplace_back(Name, Ty, nullptr);
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

    for (size_t I = 0; I != Fn.Preconditions.size(); ++I) {
      if (!WrittenPreconditions && I < Fn.ExplicitPreconditionCount)
        continue;
      CloneCtx PCtx{Renames, OldState, false};
      P.EntryOrigins.push_back(I < Fn.ExplicitPreconditionCount ? "pre"
                                                                : "entry");
      P.EntryAssumes.push_back(cloneExpr(Fn.Preconditions[I].get(), PCtx));
    }
    P.PreconditionCount = P.EntryAssumes.size();
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
      P.EntryOrigins.insert(P.EntryOrigins.end(), 2, "null");
    }
    // A field parameter is its field's value at entry, by definition: a fact
    // without definedness, since it says nothing where the field cannot be
    // read, and which a call needs not establish, as it binds the parameter
    // to the field itself.
    for (const auto &[Name, Field] : Fn.FieldParams) {
      CloneCtx PCtx{Renames, OldState, false};
      VVarExpr Parameter(Name, Field->Ty, Field->Loc);
      P.EntryAssumes.push_back(makeEq(cloneExpr(&Parameter, PCtx),
                                      cloneExpr(Field.get(), PCtx),
                                      Field->Loc));
      P.EntryOrigins.push_back("field");
    }
    if (Fn.ObjectModel) {
      CloneCtx PCtx{Renames, OldState, false};
      for (const AbstractObject &Object : abstractObjects(Fn)) {
        P.EntryAssumes.push_back(cloneExpr(
            objectPlacement(Object, SourceLocation()).get(), PCtx));
        P.EntryOrigins.push_back("object");
      }
    }
    return Renames;
  }

  /// A constructor's object at its end: every leaf initialized, each a check
  /// at its member's declaration.
  void
  emitConstructedChecks(PassiveProgram &P,
                        const std::map<std::string, std::string> &Renames) {
    const VObjectLayout *Layout = constructedLayout(Fn);
    auto Leaves = Layout ? expandedLeaves(*Layout, 4096) : std::nullopt;
    if (!Leaves) {
      P.ExitAsserts.push_back({ProofObligationKind::Unsupported,
                               makeBoolLiteral(false, Fn.DeclLoc),
                               "a constructor whose object has no known "
                               "layout"});
      return;
    }
    CloneCtx Ctx{Renames, OldState, false};
    for (const auto &[Offset, Leaf] : *Leaves) {
      const SourceLocation At = Leaf->Loc.isValid() ? Leaf->Loc : Fn.DeclLoc;
      VVarExpr This("this", VType::makePtr(), At);
      P.ExitAsserts.push_back(
          {ProofObligationKind::Initialization,
           std::make_unique<VUnaryOpExpr>(
               VUnaryOp::InitializedPtr,
               addBytes(cloneExpr(&This, Ctx),
                        std::make_unique<VLiteralExpr>(std::to_string(Offset),
                                                       pointerOffsetType(), At),
                        At),
               VType::makeBool(), At, "", "",
               stateHeapName(Ctx, VInitializationHeapName, ""))});
    }
  }

  PassiveProgram run() {
    PassiveProgram P;
    P.FunctionName = Fn.Name;
    P.FunctionIdentity = Fn.Identity;
    std::map<std::string, std::string> Renames =
        enter(P, /*WrittenPreconditions=*/true);
    for (const auto &[Name, Assumes] : Fn.Behaviors) {
      CloneCtx PCtx{Renames, OldState, false};
      P.BehaviorAssumes.emplace_back(Name, cloneExpr(Assumes.get(), PCtx));
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
      const bool OfParameter =
          llvm::any_of(Fn.Params, [&, &Name = Name](const auto &P) {
            return Name == P.first ||
                   llvm::StringRef(Name).starts_with(P.first + ".");
          });
      if (OfParameter)
        PostRenames[Name] = static_cast<const VVarExpr &>(*Entry).Name;
    }
    if (Fn.IsConstructor)
      emitConstructedChecks(P, Renames);
    // Postconditions are evaluated in order: a clause is evaluated where the
    // clauses before it hold.
    std::unique_ptr<VExpr> EarlierPosts;
    auto afterEarlier = [&](std::unique_ptr<VExpr> Cond) {
      if (!EarlierPosts)
        return Cond;
      const SourceLocation Loc = Cond->Loc, Begin = Cond->BeginLoc,
                           End = Cond->EndLoc;
      auto Guarded = makeOr(makeNot(cloneVExpr(EarlierPosts.get()), Loc),
                            std::move(Cond), Loc);
      Guarded->BeginLoc = Begin;
      Guarded->EndLoc = End;
      return Guarded;
    };
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
      if (Fn.IsProof && !Fn.IsSpec)
        P.ContractConclusions.push_back(cloneVExpr(BoundPost.get()));
      SafetyChecks Checks;
      collectSafety(Post, &FnMap, &Fn.ValidExtents,
                    &SourcePointerParameterNames, Checks, Fn.ObjectModel,
                    &OriginObjects, &Fn.OutParameters);
      if (!Fn.TotalExpressions && I < Fn.PostconditionChecks.size())
        for (const VMemoryCheck &Check : Fn.PostconditionChecks[I])
          Checks.push_back({Check.Kind, cloneVExpr(Check.Cond.get())});
      groupByKind(Checks);
      for (const SafetyCheck &Check : Checks) {
        if (Fn.TotalExpressions && isDefinedness(Check.Kind))
          continue;
        // Anchored at the clause, the operation being its focus; an unfolded
        // helper's operators may lie in another file.
        P.ExitAsserts.push_back(
            {Check.Kind, afterEarlier(cloneExpr(Check.Cond.get(), PCtx)), "",
             {Post->Loc, Post->BeginLoc, Post->EndLoc}});
      }
      auto Clause = cloneVExpr(BoundPost.get());
      EarlierPosts = EarlierPosts ? makeAnd(std::move(EarlierPosts),
                                            std::move(Clause), Post->Loc)
                                  : std::move(Clause);
      for (auto &[Kind, Part, Note] :
           checkedClause(postconditionKind(Fn, I), std::move(BoundPost),
                         UninitializedResultNote))
        P.ExitAsserts.push_back({Kind, std::move(Part), std::move(Note)});
    }
    if (Fn.IsProof && !Fn.IsSpec)
      for (const auto &[Name, Entry] : OldState)
        if (Entry->K == VExpr::Var)
          P.EntryVariables.insert(static_cast<const VVarExpr &>(*Entry).Name);
    finish(P, PostRenames);
    return P;
  }

  /// The contract's own definedness, as Dafny checks a method's
  /// well-formedness: each written precondition is defined where the ones
  /// before it hold, and is then assumed. For a function whose body is not
  /// verified, each written postcondition is checked the same way in every
  /// state the function may return in: within its frame, with any result.
  /// A body's own final state checks its postconditions in run().
  PassiveProgram contract() {
    PassiveProgram P;
    P.FunctionName = Fn.Name + ".contract";
    P.FunctionIdentity = Fn.Identity + "::contract";
    std::map<std::string, std::string> Renames =
        enter(P, /*WrittenPreconditions=*/false);
    auto checkThenAssume =
        [&](const VExpr *Clause,
            const std::vector<std::vector<VMemoryCheck>> &Recorded, size_t I) {
          CloneCtx Ctx{Renames, OldState, false};
          auto Bound = cloneExpr(Clause, Ctx);
          emitExprSafety(P, Bound.get(), nullptr, Clause->Loc, Renames, false,
                         Clause, I < Recorded.size() ? &Recorded[I] : nullptr);
          emitPassive(P, PassiveStmt::Assume, std::move(Bound), nullptr,
                      Clause->Loc);
        };
    for (unsigned I = 0;
         I < Fn.ExplicitPreconditionCount && I < Fn.Preconditions.size(); ++I) {
      llvm::SaveAndRestore<std::string> Stated(Origin, "pre");
      checkThenAssume(Fn.Preconditions[I].get(), Fn.PreconditionChecks, I);
    }
    // Storage the function allocates or frees is not modeled at a call, so
    // no caller relies on its postconditions.
    if (Fn.IsExternalContract && !Fn.UsesDynamicStorage) {
      llvm::SaveAndRestore<std::string> Returned(Origin, "ret");
      returnAnywhere(P, Renames);
      // What the calling convention says of the result holds first.
      for (size_t I = 0; I != Fn.Postconditions.size(); ++I)
        if (postconditionKind(Fn, I) != ProofObligationKind::Postcondition) {
          CloneCtx Ctx{Renames, OldState, false};
          emitPassive(P, PassiveStmt::Assume,
                      cloneExpr(Fn.Postconditions[I].get(), Ctx), nullptr,
                      Fn.Postconditions[I]->Loc);
        }
      for (size_t I = 0; I != Fn.Postconditions.size(); ++I)
        if (postconditionKind(Fn, I) == ProofObligationKind::Postcondition) {
          llvm::SaveAndRestore<std::string> Stated(Origin, "post");
          checkThenAssume(Fn.Postconditions[I].get(), Fn.PostconditionChecks,
                          I);
        }
    }
    finish(P, Renames);
    return P;
  }

  /// A return in any state the function's frame allows, as its callers see
  /// it: its footprints hold unknown values, and so does its result.
  void returnAnywhere(PassiveProgram &P,
                      std::map<std::string, std::string> &Renames) {
    const std::string EntryHeap = Renames[VHeapName];
    CloneCtx Ctx{Renames, OldState, false};
    std::map<std::string, std::unique_ptr<VExpr>> ParamMap;
    for (const auto &[Name, Ty] : Fn.Params)
      ParamMap[Name] =
          std::make_unique<VVarExpr>(Renames[Name], Ty, Fn.DeclLoc);
    std::vector<std::unique_ptr<VExpr>> Footprints;
    std::vector<std::unique_ptr<VExpr>> Counts;
    for (const VFootprint &M : Fn.Modifies) {
      Footprints.push_back(
          substParams(M.Target.get(), ParamMap, Ctx, EntryHeap, EntryHeap));
      Counts.push_back(M.Count ? substParams(M.Count.get(), ParamMap, Ctx,
                                             EntryHeap, EntryHeap)
                               : nullptr);
    }
    havocFootprints(P, Renames, Fn, Footprints, Counts, ParamMap, Ctx,
                    EntryHeap, hasImplicitHeapEffect(Fn, FnMap), Fn.DeclLoc);
    if (Fn.ReturnType.Kind == VTypeKind::Struct) {
      for (const auto &[Field, Ty] : Fn.ReturnFields) {
        const std::string Name = "result." + Field;
        Renames[Name] = bump(Name);
        Types[Name] = Ty;
      }
    } else if (Fn.ReturnType.Kind != VTypeKind::Void) {
      Renames["result"] = bump(ResultVar);
      P.ResultVarName = Renames["result"];
    }
  }

  /// What every program of the function carries: its state variables, the
  /// specs it may use, and their facts. PostRenames names the final state.
  void finish(PassiveProgram &P,
              const std::map<std::string, std::string> &PostRenames) {
    P.OldHeapName = EntryHeapVersion;
    P.HeapVariables = HeapVariables;
    P.ModelVariables = std::move(ModelVariables);
    P.TraceEvents = std::move(TraceEvents);
    P.SpecFunctions = FnMap;
    P.SpecFuel = Fn.SpecFuel;
    P.HiddenSpecs = Fn.HiddenSpecs;
    P.RevealedSpecs = Fn.RevealedSpecs;
    P.CallerIntMode = Fn.IntMode;
    addFrameInstances(P, FnMap);
    // The measure at entry, below which the function's cluster may be used.
    std::vector<std::unique_ptr<VExpr>> EntryMeasure;
    if (!Fn.Cluster.empty()) {
      CloneCtx MeasureCtx{PostRenames, OldState, false};
      for (const auto &Decrease : Fn.Decreases)
        EntryMeasure.push_back(cloneExpr(Decrease.get(), MeasureCtx));
    }
    NodeBudget Facts;
    addSpecPostInstances(P, FnMap, Fn, UnfoldingDepth, UnfoldingFuel,
                         EntryMeasure);
    if (Facts.exceeded())
      P.TooLarge = specFactsOversize(Facts);
  }

  /// In the object model a pointer without provenance is valid where it lies
  /// in one of the caller's objects or is a known valid object of its own,
  /// and abstract storage is initialized, but for an out-parameter's.
  std::unique_ptr<VExpr>
  abstractValidity(std::unique_ptr<VExpr> E,
                   const std::map<std::string, std::string> &Renames) {
    if (!E)
      return E;
    switch (E->K) {
    case VExpr::UnaryOp: {
      auto *U = static_cast<VUnaryOpExpr *>(E.get());
      if (U->Op == VUnaryOp::InitializedPtr &&
          tracksInitialization(U->Operand.get()))
        return E;
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

  /// The cells footprint I of Callee covers at a call, its Target and Count
  /// in the caller's state, where they are known: a range, a cell, or in
  /// the object model the object its region names.
  std::optional<Region>
  footprintBytes(const VFunction &Callee, size_t I, const VExpr *Target,
                 const VExpr *Count,
                 const std::map<std::string, std::unique_ptr<VExpr>> &ParamMap,
                 const CloneCtx &Ctx, const std::string &EntryHeap,
                 SourceLocation Loc) {
    const auto *Actual = Target && Target->K == VExpr::Load
                             ? static_cast<const VLoadExpr *>(Target)
                             : nullptr;
    if (!Actual)
      return std::nullopt;
    const VFootprint &Declared = Callee.Modifies[I];
    if (Count)
      return rangeBytes(Actual->Ptr.get(), Count, Declared.ElementSize, Loc);
    if (!isRegionFootprint(Declared, Callee.ScalarReferenceParams))
      return cellRegion(Actual->Ptr.get(), Actual->Ty, Loc);
    if (!Callee.ObjectModel)
      return std::nullopt;
    const VExpr *Base = addressRoot(
        static_cast<const VLoadExpr *>(Declared.Target.get())->Ptr.get());
    if (!Base || Base->K != VExpr::Var)
      return std::nullopt;
    const uint64_t Stride = std::max<uint64_t>(Base->Ty.PointeeSizeBytes, 1);
    for (const VValidExtent &Extent : Callee.ValidExtents)
      if (Extent.Base == static_cast<const VVarExpr *>(Base)->Name) {
        auto Length =
            substParams(Extent.Length.get(), ParamMap, Ctx, EntryHeap);
        return rangeBytes(Actual->Ptr.get(), Length.get(), Stride, Loc);
      }
    // A single scalar object is one heap cell.
    if (Actual->Ty.isInt() || Actual->Ty.Kind == VTypeKind::Bool ||
        Actual->Ty.Kind == VTypeKind::Ptr)
      return cellRegion(Actual->Ptr.get(), Actual->Ty, Loc);
    return Region{
        cloneVExpr(Actual->Ptr.get()),
        addBytes(cloneVExpr(Actual->Ptr.get()),
                 std::make_unique<VLiteralExpr>(std::to_string(Stride),
                                                pointerOffsetType(), Loc),
                 Loc)};
  }

  /// A record in local or dynamic storage, or in an out-parameter's, passed
  /// to a parameter that addresses one: the generated validity clause names
  /// its first byte, and the callee reads every leaf as valid and
  /// initialized storage. Each byte up to its last belongs to the live
  /// allocation of its first when the last does (an allocation's bytes are
  /// contiguous), and each leaf must be initialized unless the callee's
  /// parameter is an out-parameter.
  void emitRecordActualChecks(
      PassiveProgram &P, const VFunction &Callee,
      const std::set<std::string> &DynamicParams,
      const std::map<std::string, std::unique_ptr<VExpr>> &ParamMap,
      const CloneCtx &Ctx, SourceLocation Loc) {
    if (!Fn.ObjectModel)
      return;
    for (const auto &[Name, Identity] : Callee.RecordParams) {
      auto Actual = ParamMap.find(Name);
      const bool Dynamic = DynamicParams.count(Name);
      if (Actual == ParamMap.end() ||
          !(Dynamic || tracksInitialization(Actual->second.get())))
        continue;
      const auto Layout =
          llvm::find_if(Callee.Layouts, [&](const VObjectLayout &L) {
            return L.TypeIdentity == Identity;
          });
      if (Layout == Callee.Layouts.end() || Layout->SizeBytes == 0)
        continue;
      auto Offset = [&](uint64_t Bytes) {
        return addBytes(cloneVExpr(Actual->second.get()),
                        std::make_unique<VLiteralExpr>(
                            std::to_string(Bytes), pointerOffsetType(), Loc),
                        Loc);
      };
      if (Dynamic)
        emitPassive(P, PassiveStmt::Assert,
                    std::make_unique<VUnaryOpExpr>(
                        VUnaryOp::ValidPtr, Offset(Layout->SizeBytes - 1),
                        VType::makeBool(), Loc,
                        stateHeapName(Ctx, VAllocationHeapName, ""),
                        stateHeapName(Ctx, VLivenessHeapName, "")),
                    nullptr, Loc, ProofObligationKind::PointerValidity);
      // A constructor's object is what it initializes, and an out-parameter
      // is written before it is read.
      if ((Callee.IsConstructor && Name == "this") ||
          Callee.OutParameters.count(Name))
        continue;
      std::vector<uint64_t> Leaves;
      for (const VObjectLeaf &Leaf : Layout->Leaves) {
        std::vector<uint64_t> Offsets = {Leaf.OffsetBytes};
        for (const VObjectRepeat &Repeat : Leaf.Repeats) {
          std::vector<uint64_t> Next;
          for (uint64_t Base : Offsets)
            for (uint64_t K = 0; K < Repeat.Count && Next.size() <= 4096; ++K)
              Next.push_back(Base + K * Repeat.StrideBytes);
          Offsets = std::move(Next);
        }
        Leaves.insert(Leaves.end(), Offsets.begin(), Offsets.end());
      }
      std::unique_ptr<VExpr> Initialized;
      if (Leaves.size() <= 4096)
        for (uint64_t Leaf : Leaves) {
          auto One = std::make_unique<VUnaryOpExpr>(
              VUnaryOp::InitializedPtr, Offset(Leaf), VType::makeBool(), Loc,
              "", "", stateHeapName(Ctx, VInitializationHeapName, ""));
          Initialized =
              Initialized ? makeAnd(std::move(Initialized), std::move(One), Loc)
                          : std::move(One);
        }
      emitPassive(P, PassiveStmt::Assert,
                  Initialized ? std::move(Initialized)
                              : makeBoolLiteral(Leaves.empty(), Loc),
                  nullptr, Loc, ProofObligationKind::Unsupported,
                  OutParameterNote);
    }
  }

  /// The heap after a call of Callee whose footprints are ActualModifies
  /// (with ActualCounts) in the caller's state: each one it may write gets
  /// unknown contents, as a chain of stores when all are cells, and every
  /// other cell keeps its value; a callee whose writes are not stated, or
  /// not known, may write the whole heap. Returns the cells it writes when
  /// those are all it writes.
  std::optional<std::vector<std::unique_ptr<VExpr>>>
  havocFootprints(PassiveProgram &P,
                  std::map<std::string, std::string> &Renames,
                  const VFunction &Callee,
                  const std::vector<std::unique_ptr<VExpr>> &ActualModifies,
                  const std::vector<std::unique_ptr<VExpr>> &ActualCounts,
                  const std::map<std::string, std::unique_ptr<VExpr>> &ParamMap,
                  const CloneCtx &Ctx, const std::string &EntryHeap,
                  bool HasImplicitHeapEffect, SourceLocation Loc) {
    // A footprint in a record that a parameter addresses is its bytes there,
    // in local or dynamic storage too, and never the one cell at its start.
    auto InRecordParam = [&](size_t I) {
      const VExpr *Target = Callee.Modifies[I].Target.get();
      const VExpr *Root =
          Target && Target->K == VExpr::Load
              ? addressRoot(static_cast<const VLoadExpr *>(Target)->Ptr.get())
              : nullptr;
      return Root && Root->K == VExpr::Var &&
             Callee.RecordParams.count(
                 static_cast<const VVarExpr *>(Root)->Name);
    };
    bool CanFrameExactly = !ActualModifies.empty();
    for (size_t I = 0; I < ActualModifies.size(); ++I)
      if (!ActualModifies[I] || ActualModifies[I]->K != VExpr::Load ||
          ActualCounts[I] ||
          (isRegionFootprint(Callee.Modifies[I],
                             Callee.ScalarReferenceParams) &&
           (!hasPointerProvenance(
                static_cast<const VLoadExpr *>(ActualModifies[I].get())
                    ->Ptr.get()) ||
            InRecordParam(I))))
        CanFrameExactly = false;
    // A region footprint is its actual's object: the callee's extent, or one
    // object; in the object model the callee writes nowhere else.
    std::vector<Region> CallRegions;
    bool CanFrameRegions = Fn.ObjectModel && Callee.ObjectModel &&
                           !CanFrameExactly && !ActualModifies.empty() &&
                           !HasImplicitHeapEffect;
    // The object of a record parameter is its leaves, each one cell, so the
    // frame stays a chain of stores: the callee's stores are at its leaves.
    auto RecordCells = [&](size_t I) -> std::optional<std::vector<Region>> {
      if (!InRecordParam(I) ||
          !isRegionFootprint(Callee.Modifies[I],
                             Callee.ScalarReferenceParams) ||
          !ActualModifies[I] || ActualModifies[I]->K != VExpr::Load ||
          ActualCounts[I])
        return std::nullopt;
      const auto *Root = static_cast<const VVarExpr *>(addressRoot(
          static_cast<const VLoadExpr *>(Callee.Modifies[I].Target.get())
              ->Ptr.get()));
      if (llvm::any_of(Callee.ValidExtents, [&](const VValidExtent &Extent) {
            return Extent.Base == Root->Name;
          }))
        return std::nullopt;
      const std::string &Identity = Callee.RecordParams.at(Root->Name);
      auto Layout = llvm::find_if(Callee.Layouts, [&](const VObjectLayout &L) {
        return L.TypeIdentity == Identity;
      });
      if (Layout == Callee.Layouts.end())
        return std::nullopt;
      auto Leaves = expandedLeaves(*Layout, 4096);
      if (!Leaves || Leaves->empty())
        return std::nullopt;
      const VExpr *Object =
          static_cast<const VLoadExpr *>(ActualModifies[I].get())->Ptr.get();
      std::vector<Region> Cells;
      for (const auto &[Offset, Leaf] : *Leaves) {
        auto Address =
            addBytes(cloneVExpr(Object),
                     std::make_unique<VLiteralExpr>(std::to_string(Offset),
                                                    pointerOffsetType(), Loc),
                     Loc);
        Cells.push_back(cellRegion(Address.get(), Leaf->Ty, Loc));
      }
      return Cells;
    };
    for (size_t I = 0; CanFrameRegions && I < ActualModifies.size(); ++I) {
      if (auto Cells = RecordCells(I)) {
        for (Region &Cell : *Cells)
          CallRegions.push_back(std::move(Cell));
        continue;
      }
      std::optional<Region> Bytes;
      if (ActualModifies[I] && ActualModifies[I]->K == VExpr::Load &&
          (!hasPointerProvenance(
               static_cast<const VLoadExpr *>(ActualModifies[I].get())
                   ->Ptr.get()) ||
           InRecordParam(I)))
        Bytes = footprintBytes(Callee, I, ActualModifies[I].get(),
                               ActualCounts[I].get(), ParamMap, Ctx, EntryHeap,
                               Loc);
      if (!Bytes) {
        CanFrameRegions = false;
        break;
      }
      CallRegions.push_back(std::move(*Bytes));
    }
    const bool OnlyCells =
        llvm::all_of(CallRegions, [](const Region &R) { return R.Cell; });
    std::vector<std::unique_ptr<VExpr>> Cells;
    if (CanFrameRegions && OnlyCells) {
      // Each cell gets an unknown value and every other cell keeps its own.
      std::string PreviousHeap = EntryHeap;
      for (const Region &R : CallRegions) {
        Cells.push_back(cloneVExpr(R.Lo.get()));
        std::string NextHeap = bump(VHeapName);
        auto Fresh =
            std::make_unique<VVarExpr>(bump("__call_heap_value"), *R.Cell, Loc);
        emitPassive(P, PassiveStmt::Assume,
                    std::make_unique<VHeapStoreExpr>(PreviousHeap, NextHeap,
                                                     cloneVExpr(R.Lo.get()),
                                                     std::move(Fresh), Loc));
        PreviousHeap = NextHeap;
      }
      Renames[VHeapName] = PreviousHeap;
    } else if (CanFrameRegions) {
      std::string NextHeap = bump(VHeapName);
      emitPassive(P, PassiveStmt::Assume,
                  heapFrame(EntryHeap, NextHeap, CallRegions, Loc));
      Renames[VHeapName] = NextHeap;
      return std::nullopt;
    } else if ((!ActualModifies.empty() && !CanFrameExactly) ||
               HasImplicitHeapEffect) {
      Renames[VHeapName] = bump(VHeapName);
      return std::nullopt;
    } else if (CanFrameExactly) {
      std::string PreviousHeap = EntryHeap;
      for (const auto &M : ActualModifies) {
        const auto *L = static_cast<const VLoadExpr *>(M.get());
        Cells.push_back(cloneVExpr(L->Ptr.get()));
        std::string NextHeap = bump(VHeapName);
        auto Fresh =
            std::make_unique<VVarExpr>(bump("__call_heap_value"), L->Ty, Loc);
        emitPassive(P, PassiveStmt::Assume,
                    std::make_unique<VHeapStoreExpr>(PreviousHeap, NextHeap,
                                                     cloneVExpr(L->Ptr.get()),
                                                     std::move(Fresh), Loc));
        PreviousHeap = NextHeap;
      }
      Renames[VHeapName] = PreviousHeap;
    }
    return Cells;
  }

  /// The initialization heap Final after writes to Cells alone, from
  /// Previous: each may become initialized, none stops being, and every
  /// other address keeps its state.
  void initializeCells(PassiveProgram &P, std::string Previous,
                       const std::string &Final,
                       const std::vector<const VExpr *> &Cells,
                       const char *Written, const VExpr *Guard,
                       SourceLocation Loc) {
    for (size_t I = 0; I != Cells.size(); ++I) {
      const std::string Next =
          I + 1 == Cells.size() ? Final : bump(VInitializationHeapName);
      auto Was = std::make_unique<VLoadExpr>(cloneVExpr(Cells[I]),
                                             VType::makeBool(), Loc, Previous);
      auto Wrote =
          std::make_unique<VVarExpr>(bump(Written), VType::makeBool(), Loc);
      emitPassive(P, PassiveStmt::Assume,
                  std::make_unique<VHeapStoreExpr>(
                      Previous, Next, cloneVExpr(Cells[I]),
                      makeOr(std::move(Was), std::move(Wrote), Loc), Loc),
                  Guard, Loc);
      Previous = Next;
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
    // A field's entry value is the field at the arguments, before the call.
    for (const auto &[Name, Field] : Callee->FieldParams)
      ParamMap[Name] = substParams(Field.get(), ParamMap, Ctx, EntryHeap);
    std::set<std::string> DynamicParams;
    std::set<std::pair<std::string, std::string>> ActiveScans;
    for (const auto &Param : Callee->Params)
      if (auto It = ParamMap.find(Param.first);
          It != ParamMap.end() && hasPointerProvenance(It->second.get())) {
        DynamicParams.insert(Param.first);
        // A record a function in the object model reaches through the
        // parameter is accessed only inside it, at any field or element.
        const bool RecordObject =
            Fn.ObjectModel && Callee->RecordParams.count(Param.first);
        if (Callee->IsProof || Callee->IsExternalContract ||
            !(RecordObject
                  ? keepsNoAddress(*Callee, Param.first, /*AllowExtent=*/false,
                                   FnMap, ActiveScans)
                  : scalarDynamicCalleeSafe(*Callee, Param.first, FnMap,
                                            ActiveScans))) {
          emitPassive(P, PassiveStmt::Assert, makeBoolLiteral(false, C.Loc),
                      nullptr, C.Loc, ProofObligationKind::Unsupported,
                      "the address of local or dynamic storage is passed to " +
                          C.Callee +
                          (RecordObject
                               ? ", which may keep or free it"
                               : ", which may keep, offset, or free it") +
                          ", or has no verified body");
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
      // In the object model a pointer parameter without an extent addresses
      // one object of its pointee type: a slice of one element.
      std::vector<VValidExtent> CallerExtents;
      for (const VValidExtent &Outer : ActiveValidExtents)
        CallerExtents.emplace_back(Outer.Base, Outer.PointerType,
                                   cloneVExpr(Outer.Length.get()));
      if (Fn.ObjectModel) {
        CloneCtx EntryCtx{Renames, OldState, true};
        for (const auto &[Name, Ty] : Fn.Params)
          if (Ty.Kind == VTypeKind::Ptr && Ty.PointeeSizeBytes > 0 &&
              llvm::none_of(Fn.ValidExtents,
                            [&, &Name = Name](const VValidExtent &Outer) {
                              return Outer.Base == Name;
                            }))
            CallerExtents.emplace_back(
                stateVariableName(EntryCtx, Name), Ty,
                std::make_unique<VLiteralExpr>(1, Length->Ty, C.Loc));
      }
      auto Contained = sliceContainment(Actual->second.get(), Length.get(),
                                        Extent.PointerType.PointeeSizeBytes,
                                        CallerExtents, C.Loc);
      // A slice argument the syntactic rule cannot place (a copy, a choice,
      // a callee's result) is contained through the objects it may address.
      const VExpr *Arg = nullptr;
      for (unsigned I = 0; I < Callee->Params.size() && I < C.Args.size(); ++I)
        if (Callee->Params[I].first == Extent.Base)
          Arg = C.Args[I].get();
      // A field's value, read from memory, may address any caller object.
      if (!Arg && llvm::any_of(Callee->FieldParams, [&](const auto &Entry) {
            return Entry.first == Extent.Base;
          }))
        Arg = Actual->second.get();
      auto Bytes = scaledExtent(Length.get(),
                                Extent.PointerType.PointeeSizeBytes, C.Loc);
      auto NonNegative = asPointerOffset(Length.get());
      if (Fn.ObjectModel && Arg && Bytes && NonNegative &&
          isFalseLiteral(Contained.get()))
        Contained = makeAnd(
            std::make_unique<VBinOpExpr>(
                VBinOp::Ge, std::move(NonNegative),
                std::make_unique<VLiteralExpr>(0, pointerOffsetType(), C.Loc),
                VType::makeBool(), C.Loc),
            objectContainment(Arg, Actual->second.get(), std::move(Bytes),
                              Renames, C.Loc),
            C.Loc);
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

    // An argument that addresses a subobject passes only the bytes its
    // bounds name: the callee's extent, or its one object, lies in them.
    if (Fn.ObjectModel)
      for (unsigned I = 0; I < Callee->Params.size() && I < C.Args.size();
           ++I) {
        const auto &[Name, Ty] = Callee->Params[I];
        const VExpr *Arg = C.Args[I].get();
        if (Ty.Kind != VTypeKind::Ptr ||
            !hasBoundedRoot(Arg, Fn.BoundedPointers))
          continue;
        std::unique_ptr<VExpr> Bytes;
        for (const VValidExtent &Extent : Callee->ValidExtents)
          if (Extent.Base == Name) {
            auto Length =
                substParams(Extent.Length.get(), ParamMap, Ctx, EntryHeap);
            Bytes = scaledExtent(Length.get(),
                                 Extent.PointerType.PointeeSizeBytes, C.Loc);
          }
        if (!Bytes && Ty.PointeeSizeBytes > 0)
          Bytes = std::make_unique<VLiteralExpr>(
              std::to_string(Ty.PointeeSizeBytes), pointerOffsetType(), C.Loc);
        if (!Bytes)
          continue;
        auto Lo = cloneExpr(
            pointerBound(Arg, /*Upper=*/false, Fn.BoundedPointers).get(), Ctx);
        auto Hi = cloneExpr(
            pointerBound(Arg, /*Upper=*/true, Fn.BoundedPointers).get(), Ctx);
        const VExpr *Actual = ParamMap[Name].get();
        auto Within =
            makeAnd(std::make_unique<VBinOpExpr>(VBinOp::Le, std::move(Lo),
                                                 cloneVExpr(Actual),
                                                 VType::makeBool(), C.Loc),
                    std::make_unique<VBinOpExpr>(
                        VBinOp::Le,
                        addBytes(cloneVExpr(Actual), std::move(Bytes), C.Loc),
                        std::move(Hi), VType::makeBool(), C.Loc),
                    C.Loc);
        emitPassive(P, PassiveStmt::Assert,
                    makeOr(makeEq(cloneVExpr(Actual),
                                  std::make_unique<VLiteralExpr>(
                                      0, VType::makePtr(), C.Loc),
                                  C.Loc),
                           std::move(Within), C.Loc),
                    nullptr, C.Loc, ProofObligationKind::Bounds);
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
    auto calleeFootprintBytes = [&](size_t I) {
      return footprintBytes(*Callee, I, ActualModifies[I].get(),
                            ActualCounts[I].get(), ParamMap, Ctx, EntryHeap,
                            C.Loc);
    };

    std::set<std::string> CalleePointerParams;
    for (const auto &[Name, Ty] : Callee->Params)
      if (Ty.Kind == VTypeKind::Ptr)
        CalleePointerParams.insert(Name);
    std::set<std::string> ContainedPointerParams;
    for (const VValidExtent &Extent : Callee->ValidExtents)
      ContainedPointerParams.insert(Extent.Base);
    // Extent arguments not written from one of the caller's parameters: their
    // validity follows from their containment in the caller's objects, not
    // from a parameter's validity at entry.
    std::set<std::string> ObjectContainedParams;
    for (unsigned I = 0; I < Callee->Params.size() && I < C.Args.size(); ++I) {
      const VExpr *Base = pointerBase(C.Args[I].get());
      const bool FromParameter =
          Base && Base->K == VExpr::Var &&
          llvm::any_of(Fn.Params, [&](const auto &Param) {
            return Param.first == static_cast<const VVarExpr *>(Base)->Name;
          });
      if (ContainedPointerParams.count(Callee->Params[I].first) &&
          !FromParameter)
        ObjectContainedParams.insert(Callee->Params[I].first);
    }
    for (size_t I = 0; I != Callee->Preconditions.size(); ++I) {
      const VExpr *Pre = Callee->Preconditions[I].get();
      auto BoundPre = substParams(Pre, ParamMap, Ctx, EntryHeap, "", {},
                                  nullptr, &ContainedPointerParams);
      // A parameter with a declared extent is the slice machinery's, whose
      // containment also places it in the caller's objects: a callee outside
      // the object model (a proof function) still states its abstract
      // validity, which that membership gives.
      if (Fn.ObjectModel &&
          (!Callee->ObjectModel ||
           llvm::none_of(ContainedPointerParams,
                         [&](const std::string &Name) {
                           return referencesVar(Pre, Name);
                         }) ||
           llvm::any_of(ObjectContainedParams, [&](const std::string &Name) {
             return referencesVar(Pre, Name);
           })))
        BoundPre = abstractValidity(std::move(BoundPre), Renames);
      BoundPre = rebaseSliceBinders(std::move(BoundPre), /*Assumed=*/false);
      SafetyChecks Checks;
      collectSafety(Pre, &FnMap, &Callee->ValidExtents, &CalleePointerParams,
                    Checks, Fn.ObjectModel);
      groupByKind(Checks);
      for (const SafetyCheck &Check : Checks)
        emitPassive(P, PassiveStmt::Assert,
                    substParams(Check.Cond.get(), ParamMap, Ctx, EntryHeap),
                    nullptr, C.Loc, Check.Kind);
      emitMathBridge(P, BoundPre.get(), nullptr, C.Loc);
      for (auto &[Kind, Part, Note] :
           checkedClause(preconditionKind(*Callee, I), std::move(BoundPre),
                         OutParameterNote)) {
        const size_t Emitted = P.Stmts.size();
        emitPassive(P, PassiveStmt::Assert, std::move(Part), nullptr, C.Loc,
                    Kind, std::move(Note));
        // The check is the call's, of a clause the callee states.
        if (P.Stmts.size() != Emitted) {
          P.Stmts.back()->Clause = {Pre->Loc, Pre->BeginLoc, Pre->EndLoc};
          P.Stmts.back()->Focus = {C.Loc, C.Loc, C.Loc};
        }
      }
    }
    emitRecordActualChecks(P, *Callee, DynamicParams, ParamMap, Ctx, C.Loc);

    // A call within the caller's recursion cycle lowers the measure below its
    // value at the caller's entry, so assuming the callee's contract there is
    // well-founded induction.
    if (!Fn.IsSpec && !Fn.Decreases.empty() &&
        (C.CalleeIdentity == Fn.Identity ||
         Fn.RecursionGroup.count(C.CalleeIdentity) ||
         Fn.Cluster.count(C.CalleeIdentity)) &&
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
        const bool ActualIsRegion = isRegionFootprint(
            Callee->Modifies[I], Callee->ScalarReferenceParams);
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
          Allowed = makeOr(std::move(Allowed),
                           std::make_unique<VBinOpExpr>(
                               VBinOp::Le, cloneVExpr(InnerBytes->Hi.get()),
                               cloneVExpr(InnerBytes->Lo.get()),
                               VType::makeBool(), C.Loc),
                           C.Loc);
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
          const bool OuterIsRegion =
              isRegionFootprint(Fn.Modifies[J], Fn.ScalarReferenceParams);
          Allowed = makeOr(
              std::move(Allowed),
              footprintWithin(CallerLoad->Ptr.get(), OuterIsRegion, OuterBytes,
                              ActualLoad->Ptr.get(), ActualIsRegion,
                              ActualCounts[I] != nullptr, InnerBytes, C.Loc),
              C.Loc);
          // A region is its parameter's object, as for a store: a callee
          // footprint through another pointer (a copy of a pointer into the
          // object) is inside where its cells lie in that object.
          const VExpr *OuterBase = pointerBase(CallerLoad->Ptr.get());
          const VExpr *InnerBase = pointerBase(ActualLoad->Ptr.get());
          const auto *DeclaredLoad =
              Fn.Modifies[J].Target && Fn.Modifies[J].Target->K == VExpr::Load
                  ? static_cast<const VLoadExpr *>(Fn.Modifies[J].Target.get())
                  : nullptr;
          const VExpr *Root =
              DeclaredLoad ? addressRoot(DeclaredLoad->Ptr.get()) : nullptr;
          const bool SameBase =
              OuterBase && InnerBase && OuterBase->K == VExpr::Var &&
              InnerBase->K == VExpr::Var &&
              static_cast<const VVarExpr *>(OuterBase)->Name ==
                  static_cast<const VVarExpr *>(InnerBase)->Name;
          if (Fn.ObjectModel && OuterIsRegion && !SameBase && Root &&
              Root->K == VExpr::Var)
            if (auto Object =
                    parameterRegion(static_cast<const VVarExpr *>(Root)->Name,
                                    Renames, C.Loc)) {
              Region Inner = InnerBytes
                                 ? Region{cloneVExpr(InnerBytes->Lo.get()),
                                          cloneVExpr(InnerBytes->Hi.get()),
                                          InnerBytes->Cell}
                                 : cellRegion(ActualLoad->Ptr.get(),
                                              ActualLoad->Ty, C.Loc);
              auto Inside =
                  makeAnd(std::make_unique<VBinOpExpr>(
                              VBinOp::Le, std::move(Object->Lo),
                              std::move(Inner.Lo), VType::makeBool(), C.Loc),
                          std::make_unique<VBinOpExpr>(
                              VBinOp::Le, std::move(Inner.Hi),
                              std::move(Object->Hi), VType::makeBool(), C.Loc),
                          C.Loc);
              Allowed = makeOr(std::move(Allowed), std::move(Inside), C.Loc);
            }
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

    auto WrittenCells =
        havocFootprints(P, Renames, *Callee, ActualModifies, ActualCounts,
                        ParamMap, Ctx, EntryHeap, HasImplicitHeapEffect, C.Loc);
    // Storage the caller tracks, passed to an out-parameter, may be
    // initialized by the call, only where it writes; what was initialized
    // stays so.
    const bool InitializesActuals = initializesActuals(*Callee, ParamMap);
    if (InitializesActuals && (!WrittenCells || !WrittenCells->empty())) {
      const std::string Before = Renames[VInitializationHeapName];
      const std::string After = bump(VInitializationHeapName);
      Renames[VInitializationHeapName] = After;
      if (WrittenCells) {
        std::vector<const VExpr *> Cells;
        for (const auto &Cell : *WrittenCells)
          Cells.push_back(Cell.get());
        initializeCells(P, Before, After, Cells, "__call_initialized", nullptr,
                        C.Loc);
      } else {
        emitPassive(P, PassiveStmt::Assume,
                    initializationKept(Before, After, C.Loc), nullptr, C.Loc);
      }
    }
    // A constructor initializes every leaf of its object, as its exit checks
    // show, so the caller's storage holds an initialized object after it.
    if (Callee->IsConstructor) {
      const VObjectLayout *Layout = constructedLayout(*Callee);
      auto Leaves = Layout ? expandedLeaves(*Layout, 4096) : std::nullopt;
      auto This = ParamMap.find("this");
      if (!Leaves || This == ParamMap.end())
        emitPassive(P, PassiveStmt::Assert, makeBoolLiteral(false, C.Loc),
                    nullptr, C.Loc, ProofObligationKind::Unsupported,
                    "a constructor whose object has no known layout");
      else
        for (const auto &[Offset, Leaf] : *Leaves)
          updateHeap(
              P, Renames, VInitializationHeapName,
              addBytes(cloneVExpr(This->second.get()),
                       std::make_unique<VLiteralExpr>(
                           std::to_string(Offset), pointerOffsetType(), C.Loc),
                       C.Loc),
              makeBoolLiteral(true, C.Loc), nullptr, C.Loc);
    }

    std::map<std::string, std::unique_ptr<VExpr>> PostParamMap;
    for (const auto &[Name, Value] : ParamMap)
      PostParamMap[Name] = cloneVExpr(Value.get());

    const size_t FirstPost = P.Stmts.size();
    for (const auto &Post : Callee->Postconditions) {
      auto PS = std::make_unique<PassiveStmt>();
      PS->K = PassiveStmt::Assume;
      PS->Origin = "call:" + Callee->Name;
      PS->Cond = rebaseSliceBinders(substParams(Post.get(), PostParamMap, Ctx,
                                                EntryHeap, "", {}, &ParamMap),
                                    /*Assumed=*/true);
      P.Stmts.push_back(std::move(PS));
    }
    if (Callee->IsTrusted && P.Stmts.size() > FirstPost) {
      P.Stmts[FirstPost]->TrustedCallee = Callee->Name;
      P.Stmts[FirstPost]->PostClauses = P.Stmts.size() - FirstPost;
      P.Stmts[FirstPost]->CallLoc = C.Loc;
    }
    // The storage a postcondition reads is initialized where it reads it, as
    // the callee's exit checks of its definedness show: that is what an
    // out-parameter gives the caller.
    if (InitializesActuals)
      for (const auto &Post : Callee->Postconditions) {
        SafetyChecks Checks;
        collectSafety(Post.get(), &FnMap, &Callee->ValidExtents,
                      &CalleePointerParams, Checks, Fn.ObjectModel, nullptr,
                      &Callee->OutParameters);
        for (const SafetyCheck &Check : Checks) {
          if (Check.Kind != ProofObligationKind::Initialization)
            continue;
          auto PS = std::make_unique<PassiveStmt>();
          PS->K = PassiveStmt::Assume;
          PS->Origin = "call:" + Callee->Name;
          PS->Cond =
              rebaseSliceBinders(substParams(Check.Cond.get(), PostParamMap,
                                             Ctx, EntryHeap, "", {}, &ParamMap),
                                 /*Assumed=*/true);
          P.Stmts.push_back(std::move(PS));
        }
      }
  }

  /// Whether a call of Callee may initialize storage the caller tracks: an
  /// out-parameter's argument is local or dynamic storage, or the caller's
  /// own out-parameter's.
  bool initializesActuals(
      const VFunction &Callee,
      const std::map<std::string, std::unique_ptr<VExpr>> &ParamMap) const {
    return llvm::any_of(Callee.OutParameters, [&](const std::string &Name) {
      auto Actual = ParamMap.find(Name);
      return Actual != ParamMap.end() &&
             tracksInitialization(Actual->second.get());
    });
  }

  // The origin of the assumptions a statement makes, before its parts name
  // their own.
  static std::string statementOrigin(const VStmt &S) {
    switch (S.K) {
    case VStmt::Assign:
      return "def";
    case VStmt::Store:
      return "store";
    case VStmt::Allocate:
    case VStmt::EndLifetime:
    case VStmt::Free:
      return "alloc";
    case VStmt::If:
      return "branch";
    case VStmt::Return:
      return "ret";
    case VStmt::While:
      return "loop";
    case VStmt::Call:
      return "call:" + static_cast<const VCallStmt &>(S).Callee;
    case VStmt::ContractAssert:
      return "check";
    case VStmt::Havoc:
      return "havoc";
    default:
      return "fact";
    }
  }

  void processStmt(const VStmt &S, PassiveProgram &P,
                   std::map<std::string, std::string> &Renames,
                   std::unique_ptr<VExpr> &Active) {
    std::optional<llvm::SaveAndRestore<std::string>> Named;
    if (S.K != VStmt::Seq && S.K != VStmt::GhostBlock)
      Named.emplace(Origin, statementOrigin(S));
    llvm::SaveAndRestore<const std::unique_ptr<VExpr> *> Defining(VersionGuard,
                                                                  &Active);
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
          const bool Region = isRegionFootprint(M, Fn.ScalarReferenceParams);
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
      emitTrace(PassiveTraceKind::HeapWrite, "store", Active.get(), St.Loc,
                std::move(TraceValues));
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
      if (tracksInitialization(St.Ptr.get()))
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
      RepresentedObjects[A.Target] = {A.AllocatedType, A.SizeBytes};

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
        emitTrace(PassiveTraceKind::Deallocation, "delete", Active.get(), F.Loc,
                  std::move(TraceValues));
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
      emitTrace(PassiveTraceKind::Deallocation, "delete", Active.get(), F.Loc,
                std::move(TraceValues));
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
      // A step of the path is one that happens: a check of the value comes
      // before the return, which a failure of the check never reaches.
      emitExprSafety(P, BoundReturn.get(), Active.get(), R.Loc, Renames, true,
                     R.Value.get());
      std::vector<PassiveTraceValue> TraceValues;
      TraceValues.push_back({"value", cloneVExpr(BoundReturn.get())});
      emitTrace(PassiveTraceKind::Return, "return", Active.get(), R.Loc,
                std::move(TraceValues));
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
                       false, Inv.get(), invariantChecks(W, Inv.get()));
        emitPassive(P, PassiveStmt::Assert, std::move(BoundInv), Active.get(),
                    Inv->Loc, ProofObligationKind::InvariantEntry);
      }

      std::set<std::string> Modified;
      for (const auto &Body : W.Body)
        collectModified(*Body, Modified);
      const bool StartsLifetime = llvm::any_of(
          W.Body, [](const auto &Body) { return startsLifetime(*Body); });
      // A loop in the object model writes only the objects its stores and
      // calls reach; the rest of the heap keeps its values.
      std::vector<Region> WriteRegions;
      bool Framed = Fn.ObjectModel && Modified.count(VHeapName) &&
                    loopWriteRegions(W.Body, Renames, Modified, WriteRegions);
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
      // A loop whose condition is the constant false changes nothing.
      std::unique_ptr<VExpr> Enters = isFalseLiteral(W.Cond.get())
                                          ? makeBoolLiteral(false, W.Loc)
                                          : cloneVExpr(Active.get());
      for (const std::string &Name : Modified) {
        auto Previous = Renames.find(Name);
        if (Previous == Renames.end())
          continue;
        const std::string PreviousName = Previous->second;
        const std::string HeadName = bump(Name);
        Renames[Name] = HeadName;
        emitInactiveFrame(P, PreviousName, HeadName, typeForName(Name),
                          Enters.get(), W.Loc);
        // Without a lifetime starting in it, a loop only initializes
        // storage, where it writes: what was initialized before it still is
        // at its head.
        if (Name == VInitializationHeapName && !StartsLifetime) {
          if (Framed && !WriteRegions.empty() &&
              llvm::all_of(WriteRegions, [](const Region &R) {
                return R.Cell.has_value();
              })) {
            std::vector<const VExpr *> Cells;
            for (const Region &R : WriteRegions)
              Cells.push_back(R.Lo.get());
            initializeCells(P, PreviousName, HeadName, Cells,
                            "__loop_initialized", Active.get(), W.Loc);
          } else {
            emitPassive(P, PassiveStmt::Assume,
                        initializationKept(PreviousName, HeadName, W.Loc),
                        Active.get(), W.Loc);
          }
        }
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
      llvm::SaveAndRestore<std::string> Head(Origin, "frame");
      if (!LoopEntryHeap.empty()) {
        // Every iteration starts with the cells outside the declared
        // footprints unchanged since the loop began.
        if (auto Regions = loopFootprintRegions(W, HeadCtx, Renames))
          emitPassive(P, PassiveStmt::Assume,
                      heapFrame(LoopEntryHeap, Renames[VHeapName], *Regions,
                                W.Loc),
                      Active.get(), W.Loc);
      }
      Origin = "inv";
      for (const auto &Inv : W.Invariants) {
        assumeInvariantSafety(P, W, Inv.get(), Active.get(), Renames, Modified);
        auto BoundInv = cloneExpr(Inv.get(), HeadCtx);
        emitPassive(P, PassiveStmt::Assume, std::move(BoundInv), Active.get(),
                    W.Loc);
      }
      Origin = "cond";

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
                       BodyRenames, false, Inv.get(),
                       invariantChecks(W, Inv.get()));
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
      Origin = "exit";
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
                       false, Inv.get(),
                       invariantChecks(*Frame.Loop, Inv.get()));
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
                     A.Cond.get(), &A.MemoryChecks);
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
      emitTrace(PassiveTraceKind::Call, Call.Callee, Active.get(),
                Call.CallSite.isValid() ? Call.CallSite.Loc : Call.Loc,
                std::move(TraceValues));
      const auto EntryRenames = Renames;
      PassiveProgram CallP;
      emitCallStmt(Call, CallP, Renames);
      for (auto &CallStmt : CallP.Stmts) {
        if (CallStmt->Cond)
          CallStmt->Cond = makeImplies(cloneVExpr(Active.get()),
                                       std::move(CallStmt->Cond), S.Loc);
        // A check of the call itself (a precondition, separation, the
        // measure) is about the call expression.
        if (Call.CallSite.isValid() && CallStmt->Focus.Loc == Call.Loc)
          CallStmt->Focus = Call.CallSite;
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
                  A.ProofKind, A.Note);
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
  PassivizerImpl Impl(Fn, FnMap, UnfoldingDepth, UnfoldingFuel);
  return Impl.run();
}

PassiveProgram Passivizer::contract(const VFunction &Fn) {
  PassivizerImpl Impl(Fn, FnMap, UnfoldingDepth, UnfoldingFuel);
  return Impl.contract();
}