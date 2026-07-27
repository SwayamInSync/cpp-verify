//===--- VCMachine.cpp ----------------------------------------------------===//
#include "VCMachine.h"
#include "../IR/VType.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/SmallString.h"

using namespace clang;
using namespace verify;

static std::unique_ptr<VCExpr> vcTrue() {
  return std::make_unique<VCExpr>(VCExpr::True);
}

static std::unique_ptr<VCExpr> vcAnd(std::unique_ptr<VCExpr> A,
                                     std::unique_ptr<VCExpr> B) {
  if (!A)
    return B;
  if (!B)
    return A;
  auto N = std::make_unique<VCExpr>(VCExpr::And);
  N->Children.push_back(std::move(A));
  N->Children.push_back(std::move(B));
  return N;
}

static std::unique_ptr<VCExpr> vcNot(std::unique_ptr<VCExpr> E) {
  auto N = std::make_unique<VCExpr>(VCExpr::Not);
  N->Children.push_back(std::move(E));
  return N;
}

static std::unique_ptr<VCExpr> vcOr(std::unique_ptr<VCExpr> A,
                                    std::unique_ptr<VCExpr> B) {
  if (!A)
    return B;
  if (!B)
    return A;
  auto N = std::make_unique<VCExpr>(VCExpr::Or);
  N->Children.push_back(std::move(A));
  N->Children.push_back(std::move(B));
  return N;
}

static bool containsHeapSelect(const VCExpr *E) {
  if (!E)
    return false;
  if (E->K == VCExpr::Select)
    return true;
  for (const auto &Child : E->Children)
    if (containsHeapSelect(Child.get()))
      return true;
  return false;
}

static bool isIntegerKind(VTypeKind Kind) {
  return Kind == VTypeKind::Int32 || Kind == VTypeKind::Int64;
}

static std::unique_ptr<VCExpr> cloneVCExpr(const VCExpr *E) {
  if (!E)
    return nullptr;
  auto Copy = std::make_unique<VCExpr>(E->K);
  Copy->TypeKind = E->TypeKind;
  Copy->IntMode = E->IntMode;
  Copy->IsSigned = E->IsSigned;
  Copy->BitWidth = E->BitWidth;
  Copy->IntVal = E->IntVal;
  Copy->BoolVal = E->BoolVal;
  Copy->Name = E->Name;
  Copy->Binder = E->Binder;
  Copy->OverflowOp = E->OverflowOp;
  Copy->SpecCallee = E->SpecCallee;
  for (const auto &Child : E->Children)
    Copy->Children.push_back(cloneVCExpr(Child.get()));
  return Copy;
}

static std::unique_ptr<VCExpr> vcBinary(VCExpr::Kind Kind,
                                        std::unique_ptr<VCExpr> L,
                                        std::unique_ptr<VCExpr> R) {
  auto N = std::make_unique<VCExpr>(Kind);
  N->TypeKind = VTypeKind::Bool;
  N->IntMode = L->IntMode;
  N->IsSigned = L->IsSigned;
  N->BitWidth = L->BitWidth;
  N->Children.push_back(std::move(L));
  N->Children.push_back(std::move(R));
  return N;
}

static std::unique_ptr<VCExpr> mathLimit(unsigned BitWidth, bool IsSigned,
                                         bool Minimum) {
  llvm::APInt Value = Minimum
                          ? (IsSigned ? llvm::APInt::getSignedMinValue(BitWidth)
                                      : llvm::APInt(BitWidth, 0))
                          : (IsSigned ? llvm::APInt::getSignedMaxValue(BitWidth)
                                      : llvm::APInt::getMaxValue(BitWidth));
  llvm::SmallString<64> Buffer;
  Value.toString(Buffer, 10, IsSigned);
  auto N = std::make_unique<VCExpr>(VCExpr::IntLit);
  N->TypeKind = BitWidth > 32 ? VTypeKind::Int64 : VTypeKind::Int32;
  N->IntMode = VIntMode::Math;
  N->IsSigned = IsSigned;
  N->BitWidth = BitWidth;
  N->IntVal = std::string(Buffer);
  return N;
}

class VCMachineBuilder {
  std::string ResultVarName;
  std::string CurHeap;
  std::map<std::string, std::string> BoundVars;
  std::map<std::string, VIntMode> BoundVarModes;
  unsigned QuantifierCounter = 0;

  static VIntMode intModeOf(const VCExpr *E) {
    if (!E)
      return VIntMode::Machine;
    return E->IntMode;
  }

  static VIntMode intModeOfVType(const VType &Ty) {
    if (Ty.Kind == VTypeKind::Int32 || Ty.Kind == VTypeKind::Int64)
      return Ty.IntMode;
    return VIntMode::Machine;
  }

  std::unique_ptr<VCExpr> toMode(std::unique_ptr<VCExpr> E, VIntMode Target) {
    if (!E)
      return E;
    if (E->TypeKind == VTypeKind::Ptr) {
      E->IntMode = Target;
      return E;
    }
    if (intModeOf(E.get()) == Target)
      return E;
    if (Target == VIntMode::Machine) {
      if (E->K == VCExpr::BvToInt && E->Children.size() == 1 &&
          E->Children[0] && E->Children[0]->IntMode == VIntMode::Machine)
        return std::move(E->Children[0]);
      switch (E->K) {
      case VCExpr::IntLit:
        E->IntMode = Target;
        return E;
      case VCExpr::Add:
      case VCExpr::Sub:
      case VCExpr::Mul:
        E->Children[0] = toMode(std::move(E->Children[0]), Target);
        E->Children[1] = toMode(std::move(E->Children[1]), Target);
        E->IntMode = Target;
        return E;
      case VCExpr::Neg:
        E->Children[0] = toMode(std::move(E->Children[0]), Target);
        E->IntMode = Target;
        return E;
      case VCExpr::Ite:
        E->Children[1] = toMode(std::move(E->Children[1]), Target);
        E->Children[2] = toMode(std::move(E->Children[2]), Target);
        E->IntMode = Target;
        return E;
      default:
        break;
      }
    }
    auto N = std::make_unique<VCExpr>(
        Target == VIntMode::Machine ? VCExpr::IntToBv : VCExpr::BvToInt);
    N->IntMode = Target;
    N->TypeKind = E->TypeKind;
    N->IsSigned = E->IsSigned;
    N->BitWidth = E->BitWidth;
    N->Children.push_back(std::move(E));
    return N;
  }

  std::pair<std::unique_ptr<VCExpr>, std::unique_ptr<VCExpr>>
  unifyIntModes(std::unique_ptr<VCExpr> L, std::unique_ptr<VCExpr> R) {
    VIntMode M = intModeOf(L.get());
    if (intModeOf(R.get()) == VIntMode::Math)
      M = VIntMode::Math;
    return {toMode(std::move(L), M), toMode(std::move(R), M)};
  }

  std::unique_ptr<VCExpr>
  exactCrossModeEquality(VCExpr::Kind Kind, std::unique_ptr<VCExpr> Machine,
                         std::unique_ptr<VCExpr> Math) {
    const unsigned BitWidth = Machine->BitWidth;
    const bool IsSigned = Machine->IsSigned;
    auto InRange = vcAnd(vcBinary(VCExpr::Ge, cloneVCExpr(Math.get()),
                                  mathLimit(BitWidth, IsSigned, true)),
                         vcBinary(VCExpr::Le, cloneVCExpr(Math.get()),
                                  mathLimit(BitWidth, IsSigned, false)));

    auto Converted = toMode(std::move(Math), VIntMode::Machine);
    if (Converted->BitWidth != BitWidth) {
      auto Resize = std::make_unique<VCExpr>(VCExpr::BvResize);
      Resize->TypeKind = Machine->TypeKind;
      Resize->IntMode = VIntMode::Machine;
      Resize->IsSigned = IsSigned;
      Resize->BitWidth = BitWidth;
      Resize->Children.push_back(std::move(Converted));
      Converted = std::move(Resize);
    }

    auto Exact =
        vcAnd(std::move(InRange),
              vcBinary(VCExpr::Eq, std::move(Machine), std::move(Converted)));
    if (Kind == VCExpr::Eq)
      return Exact;
    return vcNot(std::move(Exact));
  }

  std::unique_ptr<VCExpr> fromBin(VBinOp Op, std::unique_ptr<VCExpr> L,
                                  std::unique_ptr<VCExpr> R) {
    VCExpr::Kind K = VCExpr::Eq;
    switch (Op) {
    case VBinOp::Add:
      K = VCExpr::Add;
      break;
    case VBinOp::Sub:
      K = VCExpr::Sub;
      break;
    case VBinOp::Mul:
      K = VCExpr::Mul;
      break;
    case VBinOp::Div:
      K = VCExpr::Div;
      break;
    case VBinOp::Rem:
      K = VCExpr::Rem;
      break;
    case VBinOp::BitAnd:
      K = VCExpr::BitAnd;
      break;
    case VBinOp::BitOr:
      K = VCExpr::BitOr;
      break;
    case VBinOp::BitXor:
      K = VCExpr::BitXor;
      break;
    case VBinOp::Shl:
      K = VCExpr::Shl;
      break;
    case VBinOp::Shr:
      K = VCExpr::Shr;
      break;
    case VBinOp::Lt:
      K = VCExpr::Lt;
      break;
    case VBinOp::Le:
      K = VCExpr::Le;
      break;
    case VBinOp::Gt:
      K = VCExpr::Gt;
      break;
    case VBinOp::Ge:
      K = VCExpr::Ge;
      break;
    case VBinOp::Eq:
      K = VCExpr::Eq;
      break;
    case VBinOp::Ne:
      K = VCExpr::Ne;
      break;
    case VBinOp::And:
      K = VCExpr::And;
      break;
    case VBinOp::Or:
      K = VCExpr::Or;
      break;
    }
    bool HasPointer =
        L->TypeKind == VTypeKind::Ptr || R->TypeKind == VTypeKind::Ptr;
    bool HasBoolean =
        L->TypeKind == VTypeKind::Bool || R->TypeKind == VTypeKind::Bool;
    if ((K == VCExpr::Eq || K == VCExpr::Ne) && !HasPointer && !HasBoolean &&
        isIntegerKind(L->TypeKind) && isIntegerKind(R->TypeKind) &&
        L->IntMode != R->IntMode) {
      if (L->IntMode == VIntMode::Machine)
        return exactCrossModeEquality(K, std::move(L), std::move(R));
      return exactCrossModeEquality(K, std::move(R), std::move(L));
    }
    std::pair<std::unique_ptr<VCExpr>, std::unique_ptr<VCExpr>> Unified;
    if (K == VCExpr::Shl || K == VCExpr::Shr) {
      L = toMode(std::move(L), VIntMode::Machine);
      R = toMode(std::move(R), VIntMode::Machine);
      if (R->BitWidth != L->BitWidth) {
        auto Resize = std::make_unique<VCExpr>(VCExpr::BvResize);
        Resize->TypeKind = R->TypeKind;
        Resize->IntMode = VIntMode::Machine;
        Resize->IsSigned = R->IsSigned;
        Resize->BitWidth = L->BitWidth;
        Resize->Children.push_back(std::move(R));
        R = std::move(Resize);
      }
      Unified = std::make_pair(std::move(L), std::move(R));
    } else {
      Unified = HasPointer
                    ? std::make_pair(toMode(std::move(L), VIntMode::Math),
                                     toMode(std::move(R), VIntMode::Math))
                : HasBoolean ? std::make_pair(std::move(L), std::move(R))
                             : unifyIntModes(std::move(L), std::move(R));
    }
    auto N = std::make_unique<VCExpr>(K);
    N->IntMode = intModeOf(Unified.first.get());
    N->IsSigned = Unified.first->IsSigned;
    N->BitWidth = Unified.first->BitWidth;
    if (K == VCExpr::Eq || K == VCExpr::Ne || K == VCExpr::Lt ||
        K == VCExpr::Le || K == VCExpr::Gt || K == VCExpr::Ge ||
        K == VCExpr::And || K == VCExpr::Or)
      N->TypeKind = VTypeKind::Bool;
    else
      N->TypeKind = Unified.first->TypeKind;
    N->Children.push_back(std::move(Unified.first));
    N->Children.push_back(std::move(Unified.second));
    return N;
  }

  std::unique_ptr<VCExpr> fromQuant(const VQuantifiedExpr *Q, bool IsForall) {
    auto N =
        std::make_unique<VCExpr>(IsForall ? VCExpr::Forall : VCExpr::Exists);
    N->Binder =
        "__quant_" + std::to_string(QuantifierCounter++) + "_" + Q->Binder;
    N->Children.push_back(fromVExpr(Q->Lo.get()));
    N->Children.push_back(fromVExpr(Q->Hi.get()));
    // Quantified machine integers range over the corresponding mathematical
    // interval and are converted back to their bit-vector type at machine
    // operations. This is equivalent within the typed bounds and keeps array
    // indices in Z3's native integer sort instead of mixing quantified
    // bit-vectors with integer-addressed heaps.
    N->IntMode = VIntMode::Math;
    N->BitWidth = Q->BinderType.BitWidth;
    N->IsSigned = Q->BinderType.IsSigned;

    auto Previous = BoundVars.find(Q->Binder);
    std::string PreviousName;
    bool HadPrevious = Previous != BoundVars.end();
    if (HadPrevious)
      PreviousName = Previous->second;
    auto PreviousMode = BoundVarModes.find(Q->Binder);
    bool HadPreviousMode = PreviousMode != BoundVarModes.end();
    VIntMode SavedMode =
        HadPreviousMode ? PreviousMode->second : VIntMode::Machine;
    BoundVars[Q->Binder] = N->Binder;
    BoundVarModes[Q->Binder] = VIntMode::Machine;
    auto Body = fromVExpr(Q->Body.get());
    if (!containsHeapSelect(Body.get())) {
      BoundVarModes[Q->Binder] = VIntMode::Math;
      Body = fromVExpr(Q->Body.get());
    }
    N->Children.push_back(std::move(Body));
    if (HadPrevious)
      BoundVars[Q->Binder] = std::move(PreviousName);
    else
      BoundVars.erase(Q->Binder);
    if (HadPreviousMode)
      BoundVarModes[Q->Binder] = SavedMode;
    else
      BoundVarModes.erase(Q->Binder);
    return N;
  }

  VIntMode CallerIntMode = VIntMode::Machine;
  bool ForceCallerIntMode = false;

public:
  VCMachineBuilder(std::string ResultVar, std::string Heap, VIntMode CallerMode,
                   bool ForceCallerMode = false)
      : ResultVarName(std::move(ResultVar)), CurHeap(std::move(Heap)),
        CallerIntMode(CallerMode), ForceCallerIntMode(ForceCallerMode) {}

  std::unique_ptr<VCExpr> fromVExpr(const VExpr *E) {
    if (!E)
      return vcTrue();
    switch (E->K) {
    case VExpr::Literal: {
      const auto *L = static_cast<const VLiteralExpr *>(E);
      if (L->Ty.Kind == VTypeKind::Bool) {
        auto N = std::make_unique<VCExpr>(VCExpr::BoolLit);
        N->BoolVal = L->Value != "0";
        return N;
      }
      auto N = std::make_unique<VCExpr>(VCExpr::IntLit);
      N->IntVal = L->Value;
      N->TypeKind = L->Ty.Kind;
      N->IsSigned = L->Ty.IsSigned;
      N->BitWidth = L->Ty.BitWidth;
      N->IntMode = ForceCallerIntMode ? CallerIntMode : intModeOfVType(L->Ty);
      return N;
    }
    case VExpr::Var: {
      auto N = std::make_unique<VCExpr>(VCExpr::Var);
      const std::string &Name = static_cast<const VVarExpr *>(E)->Name;
      auto Bound = BoundVars.find(Name);
      N->Name = Bound == BoundVars.end() ? Name : Bound->second;
      N->TypeKind = static_cast<const VVarExpr *>(E)->Ty.Kind;
      N->IsSigned = static_cast<const VVarExpr *>(E)->Ty.IsSigned;
      N->BitWidth = static_cast<const VVarExpr *>(E)->Ty.BitWidth;
      N->IntMode = Bound != BoundVars.end() ? BoundVarModes.at(Name)
                   : ForceCallerIntMode
                       ? CallerIntMode
                       : intModeOfVType(static_cast<const VVarExpr *>(E)->Ty);
      return N;
    }
    case VExpr::BinOp: {
      const auto *B = static_cast<const VBinOpExpr *>(E);
      return fromBin(B->Op, fromVExpr(B->Lhs.get()), fromVExpr(B->Rhs.get()));
    }
    case VExpr::UnaryOp: {
      const auto *U = static_cast<const VUnaryOpExpr *>(E);
      if (U->Op == VUnaryOp::Neg) {
        auto N = std::make_unique<VCExpr>(VCExpr::Neg);
        N->Children.push_back(fromVExpr(U->Operand.get()));
        N->IntMode = intModeOf(N->Children[0].get());
        N->TypeKind = U->Ty.Kind;
        N->IsSigned = U->Ty.IsSigned;
        N->BitWidth = U->Ty.BitWidth;
        return N;
      }
      if (U->Op == VUnaryOp::BitNot) {
        auto N = std::make_unique<VCExpr>(VCExpr::BitNot);
        N->Children.push_back(fromVExpr(U->Operand.get()));
        N->IntMode = intModeOf(N->Children[0].get());
        N->TypeKind = U->Ty.Kind;
        N->IsSigned = U->Ty.IsSigned;
        N->BitWidth = U->Ty.BitWidth;
        return N;
      }
      if (U->Op == VUnaryOp::ValidPtr) {
        if (!U->AllocationHeapVar.empty() && !U->LivenessHeapVar.empty()) {
          auto Owner = std::make_unique<VLoadExpr>(cloneVExpr(U->Operand.get()),
                                                   VType::makePtr(), U->Loc,
                                                   U->AllocationHeapVar);
          std::unique_ptr<VExpr> HasOwner;
          if (U->Operand->K == VExpr::Var &&
              !static_cast<const VVarExpr *>(U->Operand.get())
                   ->AllocationIdentity.empty()) {
            HasOwner = std::make_unique<VBinOpExpr>(
                VBinOp::Eq, cloneVExpr(Owner.get()),
                std::make_unique<VLiteralExpr>(
                    static_cast<const VVarExpr *>(U->Operand.get())
                        ->AllocationIdentity,
                    VType::makePtr(), U->Loc),
                VType::makeBool(), U->Loc);
          } else {
            HasOwner = std::make_unique<VBinOpExpr>(
                VBinOp::Ne, cloneVExpr(Owner.get()),
                std::make_unique<VLiteralExpr>(0, VType::makePtr(), U->Loc),
                VType::makeBool(), U->Loc);
          }
          auto Live = std::make_unique<VLoadExpr>(
              std::move(Owner), VType::makeBool(), U->Loc, U->LivenessHeapVar);
          auto Valid = std::make_unique<VBinOpExpr>(
              VBinOp::And, std::move(HasOwner), std::move(Live),
              VType::makeBool(), U->Loc);
          return fromVExpr(Valid.get());
        }
        auto N = std::make_unique<VCExpr>(VCExpr::ValidPtr);
        N->Children.push_back(fromVExpr(U->Operand.get()));
        N->TypeKind = VTypeKind::Bool;
        return N;
      }
      if (U->Op == VUnaryOp::InitializedPtr) {
        if (U->InitializationHeapVar.empty()) {
          auto N = std::make_unique<VCExpr>(VCExpr::BoolLit);
          N->BoolVal = false;
          return N;
        }
        VLoadExpr Initialized(cloneVExpr(U->Operand.get()), VType::makeBool(),
                              U->Loc, U->InitializationHeapVar);
        return fromVExpr(&Initialized);
      }
      return vcNot(fromVExpr(U->Operand.get()));
    }
    case VExpr::Conditional: {
      const auto *C = static_cast<const VConditionalExpr *>(E);
      auto N = std::make_unique<VCExpr>(VCExpr::Ite);
      N->Children.push_back(fromVExpr(C->Cond.get()));
      N->Children.push_back(fromVExpr(C->Then.get()));
      N->Children.push_back(fromVExpr(C->Else.get()));
      N->TypeKind = C->Ty.Kind;
      N->IntMode = intModeOf(N->Children[1].get());
      N->IsSigned = C->Ty.IsSigned;
      N->BitWidth = C->Ty.BitWidth;
      return N;
    }
    case VExpr::Result: {
      auto N = std::make_unique<VCExpr>(VCExpr::Var);
      N->Name = ResultVarName.empty() ? "__result_0" : ResultVarName;
      N->TypeKind = E->Ty.Kind;
      N->IntMode = intModeOfVType(E->Ty);
      N->IsSigned = E->Ty.IsSigned;
      N->BitWidth = E->Ty.BitWidth;
      return N;
    }
    case VExpr::Old:
      return fromVExpr(static_cast<const VOldExpr *>(E)->Inner.get());
    case VExpr::Cast: {
      const auto *C = static_cast<const VCastExpr *>(E);
      auto Inner = fromVExpr(C->Inner.get());
      if (!Inner)
        return nullptr;
      if (C->Ty.Kind == VTypeKind::Bool && C->FromTy.Kind != VTypeKind::Bool) {
        auto Zero = std::make_unique<VCExpr>(VCExpr::IntLit);
        Zero->TypeKind = C->FromTy.Kind;
        Zero->IntMode = intModeOfVType(C->FromTy);
        Zero->IsSigned = C->FromTy.IsSigned;
        Zero->BitWidth = C->FromTy.BitWidth;
        auto N = std::make_unique<VCExpr>(VCExpr::Ne);
        N->TypeKind = VTypeKind::Bool;
        N->IntMode =
            C->FromTy.Kind == VTypeKind::Ptr ? VIntMode::Math : Inner->IntMode;
        N->IsSigned = Inner->IsSigned;
        N->BitWidth = Inner->BitWidth;
        N->Children.push_back(std::move(Inner));
        N->Children.push_back(std::move(Zero));
        return N;
      }
      if (C->FromTy.Kind == VTypeKind::Bool && C->Ty.Kind != VTypeKind::Bool) {
        auto One = std::make_unique<VCExpr>(VCExpr::IntLit);
        One->IntVal = "1";
        One->TypeKind = C->Ty.Kind;
        One->IntMode = intModeOfVType(C->Ty);
        One->IsSigned = C->Ty.IsSigned;
        One->BitWidth = C->Ty.BitWidth;
        auto Zero = std::make_unique<VCExpr>(VCExpr::IntLit);
        Zero->TypeKind = C->Ty.Kind;
        Zero->IntMode = intModeOfVType(C->Ty);
        Zero->IsSigned = C->Ty.IsSigned;
        Zero->BitWidth = C->Ty.BitWidth;
        auto N = std::make_unique<VCExpr>(VCExpr::Ite);
        N->TypeKind = C->Ty.Kind;
        N->IntMode = intModeOfVType(C->Ty);
        N->IsSigned = C->Ty.IsSigned;
        N->BitWidth = C->Ty.BitWidth;
        N->Children.push_back(std::move(Inner));
        N->Children.push_back(std::move(One));
        N->Children.push_back(std::move(Zero));
        return N;
      }
      VIntMode TargetMode = intModeOfVType(C->Ty);
      Inner = toMode(std::move(Inner), TargetMode);
      if (TargetMode == VIntMode::Machine &&
          Inner->BitWidth != C->Ty.BitWidth) {
        auto Resize = std::make_unique<VCExpr>(VCExpr::BvResize);
        Resize->TypeKind = C->Ty.Kind;
        Resize->IntMode = TargetMode;
        Resize->IsSigned = C->Ty.IsSigned;
        Resize->BitWidth = C->Ty.BitWidth;
        Resize->Children.push_back(std::move(Inner));
        Inner = std::move(Resize);
      }
      Inner->TypeKind = C->Ty.Kind;
      Inner->IsSigned = C->Ty.IsSigned;
      Inner->BitWidth = C->Ty.BitWidth;
      return Inner;
    }
    case VExpr::Load: {
      const auto *L = static_cast<const VLoadExpr *>(E);
      std::string Heap = L->HeapVar.empty() ? CurHeap : L->HeapVar;
      auto N = std::make_unique<VCExpr>(VCExpr::Select);
      N->TypeKind = L->Ty.Kind;
      N->IntMode = CallerIntMode;
      N->IsSigned = L->Ty.IsSigned;
      N->BitWidth = L->Ty.BitWidth;
      auto H = std::make_unique<VCExpr>(VCExpr::Var);
      H->Name = Heap;
      N->Children.push_back(std::move(H));
      N->Children.push_back(fromVExpr(L->Ptr.get()));
      return N;
    }
    case VExpr::Forall:
      return fromQuant(static_cast<const VQuantifiedExpr *>(E), true);
    case VExpr::Exists:
      return fromQuant(static_cast<const VQuantifiedExpr *>(E), false);
    case VExpr::HeapStore: {
      const auto *H = static_cast<const VHeapStoreExpr *>(E);
      auto N = std::make_unique<VCExpr>(VCExpr::Store);
      auto Before = std::make_unique<VCExpr>(VCExpr::Var);
      Before->Name = H->HeapBefore;
      auto After = std::make_unique<VCExpr>(VCExpr::Var);
      After->Name = H->HeapAfter;
      N->Children.push_back(std::move(Before));
      N->Children.push_back(fromVExpr(H->Ptr.get()));
      N->Children.push_back(fromVExpr(H->Val.get()));
      N->Children.push_back(std::move(After));
      return N;
    }
    case VExpr::FieldAccess: {
      const auto *F = static_cast<const VFieldAccessExpr *>(E);
      auto N = std::make_unique<VCExpr>(VCExpr::Var);
      N->Name = fieldVarName(F);
      N->TypeKind = F->Base->K == VExpr::Var || F->Base->K == VExpr::Result
                        ? F->Ty.Kind
                        : VTypeKind::Unsupported;
      N->IntMode = intModeOfVType(F->Ty);
      N->IsSigned = F->Ty.IsSigned;
      N->BitWidth = F->Ty.BitWidth;
      return N;
    }
    case VExpr::SpecCall: {
      const auto *C = static_cast<const VSpecCallExpr *>(E);
      auto N = std::make_unique<VCExpr>(VCExpr::SpecCall);
      N->SpecCallee = C->CalleeIdentity;
      N->TypeKind = C->Ty.Kind;
      N->IntMode = C->Ty.IntMode;
      N->IsSigned = C->Ty.IsSigned;
      N->BitWidth = C->Ty.BitWidth;
      for (const auto &A : C->Args) {
        auto Arg = fromVExpr(A.get());
        if (Arg && (Arg->TypeKind == VTypeKind::Int32 ||
                    Arg->TypeKind == VTypeKind::Int64))
          Arg = toMode(std::move(Arg), C->Ty.IntMode);
        N->Children.push_back(std::move(Arg));
      }
      return N;
    }
    case VExpr::OverflowCheck: {
      const auto *O = static_cast<const VOverflowCheckExpr *>(E);
      auto N = std::make_unique<VCExpr>(VCExpr::NoOverflow);
      N->TypeKind = VTypeKind::Bool;
      N->IntMode = VIntMode::Machine;
      N->IsSigned = O->Lhs->Ty.IsSigned;
      N->BitWidth = O->Lhs->Ty.BitWidth;
      N->OverflowOp = O->Op;
      N->Children.push_back(fromVExpr(O->Lhs.get()));
      if (O->Rhs)
        N->Children.push_back(fromVExpr(O->Rhs.get()));
      return N;
    }
    }
    return vcTrue();
  }

  static std::string fieldVarName(const VFieldAccessExpr *F) {
    std::string Base;
    if (F->Base->K == VExpr::Var)
      Base = static_cast<const VVarExpr *>(F->Base.get())->Name;
    else if (F->Base->K == VExpr::Result)
      Base = "result";
    else
      Base = "__cppverify_unsupported_field_base";
    return Base + "." + F->Field;
  }

  VCMachine buildPassive(const PassiveProgram &P) {
    VCMachine M;
    M.ResultVarName = P.ResultVarName;
    M.HeapPrefix =
        P.OldHeapName.empty() ? std::string(VHeapName) + "_0" : P.OldHeapName;
    M.SpecFunctions = P.SpecFunctions;
    M.SpecFuel = P.SpecFuel;
    M.HiddenSpecs = P.HiddenSpecs;
    M.RevealedSpecs = P.RevealedSpecs;
    M.CallerIntMode = P.CallerIntMode;
    CurHeap = M.HeapPrefix;

    std::unique_ptr<VCExpr> WP = vcTrue();
    for (const auto &A : P.ExitAsserts)
      WP = vcAnd(std::move(WP), fromVExpr(A.get()));

    for (auto It = P.Stmts.rbegin(); It != P.Stmts.rend(); ++It) {
      const PassiveStmt &S = **It;
      if (!S.Cond)
        continue;
      auto Cond = fromVExpr(S.Cond.get());
      if (S.K == PassiveStmt::Assume)
        WP = vcOr(vcNot(std::move(Cond)), std::move(WP));
      else
        WP = vcAnd(std::move(Cond), std::move(WP));
    }

    for (auto It = P.EntryAssumes.rbegin(); It != P.EntryAssumes.rend(); ++It)
      WP = vcOr(vcNot(fromVExpr(It->get())), std::move(WP));

    M.Goal = vcNot(std::move(WP));
    return M;
  }
};

VCMachine VCMachine::fromPassive(const PassiveProgram &P) {
  VCMachineBuilder B(P.ResultVarName,
                     P.OldHeapName.empty() ? std::string(VHeapName) + "_0"
                                           : P.OldHeapName,
                     P.CallerIntMode);
  return B.buildPassive(P);
}

VCMachine VCMachine::fromVExpr(const VExpr *E, const std::string &ResultVar,
                               const std::string &CurHeap,
                               VIntMode CallerMode) {
  VCMachineBuilder B(ResultVar, CurHeap, CallerMode);
  VCMachine M;
  M.ResultVarName = ResultVar;
  M.HeapPrefix = CurHeap;
  M.CallerIntMode = CallerMode;
  M.Goal = B.fromVExpr(E);
  return M;
}