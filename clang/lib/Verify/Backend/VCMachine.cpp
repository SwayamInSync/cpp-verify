//===--- VCMachine.cpp ----------------------------------------------------===//
#include "VCMachine.h"
#include "../IR/VType.h"

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

static int64_t evalIntLiteral(const VExpr *E) {
  if (!E || E->K != VExpr::Literal)
    return 0;
  return static_cast<const VLiteralExpr *>(E)->Value;
}

// Rename every free occurrence of a quantifier binder in an already-built VCExpr
// to a fresh name, pinning it to a 32-bit machine bit-vector so the encoder
// gives it a single, consistent Z3 const. Stops at a nested quantifier that
// re-binds the same source name (shadowing).
static void renameBinder(VCExpr *E, const std::string &Old,
                         const std::string &New) {
  if (!E)
    return;
  if (E->K == VCExpr::Forall && E->Binder == Old)
    return;
  if (E->K == VCExpr::Var && E->Name == Old) {
    E->Name = New;
    E->IsPtr = false;
    E->IntMode = VIntMode::Machine;
    E->Width = 32;
  }
  for (auto &C : E->Children)
    renameBinder(C.get(), Old, New);
}

class VCMachineBuilder {
  std::string ResultVarName;
  std::string CurHeap;

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
    if (!E || intModeOf(E.get()) == Target)
      return E;
    auto N = std::make_unique<VCExpr>(
        Target == VIntMode::Machine ? VCExpr::IntToBv : VCExpr::BvToInt);
    N->IntMode = Target;
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

  std::unique_ptr<VCExpr> fromBin(VBinOp Op, std::unique_ptr<VCExpr> L,
                                  std::unique_ptr<VCExpr> R,
                                  bool Unsigned = false) {
    VCExpr::Kind K = VCExpr::Eq;
    switch (Op) {
    case VBinOp::Add:
      K = VCExpr::Add;
      break;
    case VBinOp::Div:
      K = VCExpr::Div;
      break;
    case VBinOp::Rem:
      K = VCExpr::Rem;
      break;
    case VBinOp::Sub:
      K = VCExpr::Sub;
      break;
    case VBinOp::Mul:
      K = VCExpr::Mul;
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
    default:
      K = VCExpr::Eq;
      break;
    }
    // Pointer arithmetic / comparison: if either operand is an address, the node
    // is computed in integer (wrap-free) arithmetic.
    bool PtrOperands = L->IsPtr || R->IsPtr;
    auto Unified = unifyIntModes(std::move(L), std::move(R));
    auto N = std::make_unique<VCExpr>(K);
    N->IntMode = intModeOf(Unified.first.get());
    N->Unsigned = Unsigned;
    N->Width = std::max(Unified.first->Width, Unified.second->Width);
    N->IsPtr = PtrOperands;
    N->Children.push_back(std::move(Unified.first));
    N->Children.push_back(std::move(Unified.second));
    return N;
  }

  // Maximum concrete range to unroll into a conjunction/disjunction; beyond this
  // (or for symbolic bounds) emit a real quantifier so reasoning stays sound.
  static constexpr int64_t QuantUnrollLimit = 64;

  std::unique_ptr<VCExpr> expandQuant(const VQuantifiedExpr *Q, bool IsForall) {
    int64_t Lo = 0, Hi = 0;
    bool ConcreteLo = Q->Lo && Q->Lo->K == VExpr::Literal;
    bool ConcreteHi = Q->Hi && Q->Hi->K == VExpr::Literal;
    if (ConcreteLo)
      Lo = static_cast<const VLiteralExpr *>(Q->Lo.get())->Value;
    if (ConcreteHi)
      Hi = static_cast<const VLiteralExpr *>(Q->Hi.get())->Value;

    // Small concrete range: unroll (cheap, no quantifier instantiation cost).
    if (ConcreteLo && ConcreteHi && Hi - Lo <= QuantUnrollLimit) {
      if (Hi <= Lo)
        return std::make_unique<VCExpr>(IsForall ? VCExpr::True : VCExpr::False);
      std::unique_ptr<VCExpr> Acc =
          std::make_unique<VCExpr>(IsForall ? VCExpr::True : VCExpr::False);
      VIntMode Mode = intModeOfVType(Q->Body->Ty);
      for (int64_t I = Lo; I < Hi; ++I) {
        auto InstBody =
            substituteBinderInVExpr(Q->Body.get(), Q->Binder, I, Mode);
        auto Body = fromVExpr(InstBody.get());
        if (IsForall)
          Acc = vcAnd(std::move(Acc), std::move(Body));
        else
          Acc = vcOr(std::move(Acc), std::move(Body));
      }
      return Acc;
    }

    // Symbolic (or large) bounds: emit a real bounded quantifier
    //   forall i. (lo <= i < hi) => body      (exists: && instead of =>)
    // Alpha-rename the binder to a fresh name pinned to a 32-bit bit-vector.
    // Different quantifiers can reuse a source binder name (e.g. `i` in both a
    // loop invariant and the postcondition); the encoder caches Z3 consts by
    // name, so without a unique name they could collide and pick up an
    // inconsistent sort (int vs bit-vector) depending on encoding order.
    static unsigned QuantId = 0;
    std::string Fresh = Q->Binder + "$" + std::to_string(++QuantId);
    auto N = std::make_unique<VCExpr>(VCExpr::Forall);
    N->BoolVal = IsForall;
    N->Binder = Fresh;
    N->Children.push_back(fromVExpr(Q->Lo.get()));
    N->Children.push_back(fromVExpr(Q->Hi.get()));
    auto Body = fromVExpr(Q->Body.get());
    renameBinder(Body.get(), Q->Binder, Fresh);
    N->Children.push_back(std::move(Body));
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
        N->BoolVal = L->Value != 0;
        return N;
      }
      auto N = std::make_unique<VCExpr>(VCExpr::IntLit);
      N->IntVal = L->Value;
      N->IntMode = ForceCallerIntMode ? CallerIntMode
                                      : intModeOfVType(L->Ty);
      N->Width = L->Ty.bvWidth();
      N->IsPtr = L->Ty.Kind == VTypeKind::Ptr; // e.g. nullptr literal
      return N;
    }
    case VExpr::Var: {
      const auto *V = static_cast<const VVarExpr *>(E);
      auto N = std::make_unique<VCExpr>(VCExpr::Var);
      N->Name = V->Name;
      N->IntMode = ForceCallerIntMode ? CallerIntMode : intModeOfVType(V->Ty);
      N->Width = V->Ty.bvWidth();
      N->IsPtr = V->Ty.Kind == VTypeKind::Ptr;
      return N;
    }
    case VExpr::BinOp: {
      const auto *B = static_cast<const VBinOpExpr *>(E);
      // Operand signedness drives bvudiv/bvurem vs bvsdiv/bvsrem. Use the wider
      // operand type when available; fall back to the result type.
      bool Unsigned = B->Lhs->Ty.Unsigned || B->Rhs->Ty.Unsigned || B->Ty.Unsigned;
      return fromBin(B->Op, fromVExpr(B->Lhs.get()), fromVExpr(B->Rhs.get()),
                     Unsigned);
    }
    case VExpr::UnaryOp: {
      const auto *U = static_cast<const VUnaryOpExpr *>(E);
      if (U->Op == VUnaryOp::Neg) {
        auto N = std::make_unique<VCExpr>(VCExpr::Neg);
        N->Children.push_back(fromVExpr(U->Operand.get()));
        N->IntMode = intModeOf(N->Children[0].get());
        return N;
      }
      return vcNot(fromVExpr(U->Operand.get()));
    }
    case VExpr::Conditional: {
      const auto *C = static_cast<const VConditionalExpr *>(E);
      auto N = std::make_unique<VCExpr>(VCExpr::Ite);
      N->Children.push_back(fromVExpr(C->Cond.get()));
      N->Children.push_back(fromVExpr(C->Then.get()));
      N->Children.push_back(fromVExpr(C->Else.get()));
      N->IntMode = intModeOf(N->Children[1].get());
      return N;
    }
    case VExpr::Result: {
      auto N = std::make_unique<VCExpr>(VCExpr::Var);
      N->Name = ResultVarName.empty() ? "__result_0" : ResultVarName;
      return N;
    }
    case VExpr::Old:
      return fromVExpr(static_cast<const VOldExpr *>(E)->Inner.get());
    case VExpr::Cast:
      return fromVExpr(static_cast<const VCastExpr *>(E)->Inner.get());
    case VExpr::Load: {
      const auto *L = static_cast<const VLoadExpr *>(E);
      std::string Heap = L->HeapVar.empty() ? CurHeap : L->HeapVar;
      auto N = std::make_unique<VCExpr>(VCExpr::Select);
      N->IntMode = CallerIntMode;
      auto H = std::make_unique<VCExpr>(VCExpr::Var);
      H->Name = Heap;
      N->Children.push_back(std::move(H));
      N->Children.push_back(fromVExpr(L->Ptr.get()));
      return N;
    }
    case VExpr::Forall:
      return expandQuant(static_cast<const VQuantifiedExpr *>(E), true);
    case VExpr::Exists:
      return expandQuant(static_cast<const VQuantifiedExpr *>(E), false);
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
      return N;
    }
    case VExpr::SpecCall: {
      const auto *C = static_cast<const VSpecCallExpr *>(E);
      auto N = std::make_unique<VCExpr>(VCExpr::SpecCall);
      N->SpecCallee = C->Callee;
      N->IntMode = CallerIntMode;
      for (const auto &A : C->Args)
        N->Children.push_back(fromVExpr(A.get()));
      return N;
    }
    case VExpr::OverflowCheck: {
      const auto *O = static_cast<const VOverflowCheckExpr *>(E);
      auto N = std::make_unique<VCExpr>(VCExpr::NoOverflow);
      N->IntMode = VIntMode::Machine; // overflow only meaningful for bit-vectors
      N->IntVal = static_cast<int64_t>(O->Op);
      N->Width = O->Lhs->Ty.bvWidth();
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
      Base = "base";
    return Base + "." + F->Field;
  }

  VCMachine buildPassive(const PassiveProgram &P) {
    VCMachine M;
    M.ResultVarName = P.ResultVarName;
    M.HeapPrefix = P.OldHeapName.empty() ? std::string(VHeapName) + "_0" : P.OldHeapName;
    M.SpecFunctions = P.SpecFunctions;
    M.SpecFuel = P.SpecFuel;
    M.HiddenSpecs = P.HiddenSpecs;
    M.RevealedSpecs = P.RevealedSpecs;
    M.CallerIntMode = P.CallerIntMode;
    CurHeap = M.HeapPrefix;

    // Build the verification condition as the negated weakest precondition, so
    // each assert is checked only against the assumes that *precede* it. A flat
    // (∧assumes) ∧ ¬(∧asserts) is unsound: a later contradictory assume (e.g. a
    // loop's inductive hypothesis I ∧ cond that is unsatisfiable given the pre)
    // makes the whole goal UNSAT, vacuously "verifying" earlier asserts.
    //
    // Encode left-to-right (heap-version tracking is forward), recording each
    // assume/assert; then fold the boolean structure right-to-left:
    //   ¬wp(assume A; r) = A ∧ ¬wp(r)
    //   ¬wp(assert P; r) = ¬P ∨ ¬wp(r)
    //   ¬wp(skip)        = false
    std::vector<std::pair<bool, std::unique_ptr<VCExpr>>> Items; // (isAssume, e)

    for (const auto &A : P.EntryAssumes)
      Items.emplace_back(true, fromVExpr(A.get()));

    for (const auto &S : P.Stmts) {
      if (S->K == PassiveStmt::Assume && S->Cond) {
        auto Enc = fromVExpr(S->Cond.get());
        if (S->Cond->K == VExpr::HeapStore)
          CurHeap =
              static_cast<const VHeapStoreExpr *>(S->Cond.get())->HeapAfter;
        Items.emplace_back(true, std::move(Enc));
      } else if (S->K == PassiveStmt::Assert && S->Cond) {
        Items.emplace_back(false, fromVExpr(S->Cond.get()));
      }
    }

    for (const auto &A : P.ExitAsserts)
      Items.emplace_back(false, fromVExpr(A.get()));

    std::unique_ptr<VCExpr> G = std::make_unique<VCExpr>(VCExpr::False);
    for (auto It = Items.rbegin(); It != Items.rend(); ++It) {
      if (It->first)
        G = vcAnd(std::move(It->second), std::move(G));
      else
        G = vcOr(vcNot(std::move(It->second)), std::move(G));
    }

    M.Goal = std::move(G);
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
                               const std::string &CurHeap, VIntMode CallerMode) {
  VCMachineBuilder B(ResultVar, CurHeap, CallerMode, true);
  VCMachine M;
  M.ResultVarName = ResultVar;
  M.HeapPrefix = CurHeap;
  M.CallerIntMode = CallerMode;
  M.Goal = B.fromVExpr(E);
  return M;
}