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
    auto Unified = unifyIntModes(std::move(L), std::move(R));
    auto N = std::make_unique<VCExpr>(K);
    N->IntMode = intModeOf(Unified.first.get());
    N->Children.push_back(std::move(Unified.first));
    N->Children.push_back(std::move(Unified.second));
    return N;
  }

  std::unique_ptr<VCExpr> expandQuant(const VQuantifiedExpr *Q, bool IsForall) {
    int64_t Lo = evalIntLiteral(Q->Lo.get());
    int64_t Hi = evalIntLiteral(Q->Hi.get());
    if (Hi <= Lo)
      return std::make_unique<VCExpr>(IsForall ? VCExpr::True : VCExpr::False);
    std::unique_ptr<VCExpr> Acc =
        std::make_unique<VCExpr>(IsForall ? VCExpr::True : VCExpr::False);
    for (int64_t I = Lo; I < Hi; ++I) {
      auto Body = fromVExpr(Q->Body.get());
      auto Binder = std::make_unique<VCExpr>(VCExpr::IntLit);
      Binder->IntVal = I;
      auto Eq = std::make_unique<VCExpr>(VCExpr::Eq);
      auto Var = std::make_unique<VCExpr>(VCExpr::Var);
      Var->Name = Q->Binder;
      Eq->Children.push_back(std::move(Var));
      Eq->Children.push_back(std::move(Binder));
      auto Inst = std::make_unique<VCExpr>(VCExpr::And);
      Inst->Children.push_back(std::move(Eq));
      Inst->Children.push_back(std::move(Body));
      if (IsForall)
        Acc = vcAnd(std::move(Acc), std::move(Inst));
      else
        Acc = vcOr(std::move(Acc), std::move(Inst));
    }
    return Acc;
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
      return N;
    }
    case VExpr::Var: {
      auto N = std::make_unique<VCExpr>(VCExpr::Var);
      N->Name = static_cast<const VVarExpr *>(E)->Name;
      N->IntMode = ForceCallerIntMode
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

    std::unique_ptr<VCExpr> Hyp = vcTrue();
    std::unique_ptr<VCExpr> Post = vcTrue();

    for (const auto &A : P.EntryAssumes)
      Hyp = vcAnd(std::move(Hyp), fromVExpr(A.get()));

    for (const auto &S : P.Stmts) {
      if (S->K == PassiveStmt::Assume && S->Cond) {
        if (S->Cond->K == VExpr::HeapStore) {
          auto *H = static_cast<const VHeapStoreExpr *>(S->Cond.get());
          Hyp = vcAnd(std::move(Hyp), fromVExpr(S->Cond.get()));
          CurHeap = H->HeapAfter;
        } else {
          Hyp = vcAnd(std::move(Hyp), fromVExpr(S->Cond.get()));
        }
      } else if (S->K == PassiveStmt::Assert && S->Cond) {
        Post = vcAnd(std::move(Post), fromVExpr(S->Cond.get()));
      }
    }

    for (const auto &A : P.ExitAsserts)
      Post = vcAnd(std::move(Post), fromVExpr(A.get()));

    M.Goal = vcAnd(std::move(Hyp), vcNot(std::move(Post)));
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