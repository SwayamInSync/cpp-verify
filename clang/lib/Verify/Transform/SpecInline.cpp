//===--- SpecInline.cpp ---------------------------------------------------===//
#include "SpecInline.h"
#include "../Transform/Passivize.h"
#include <iterator>
#include <map>
#include <set>
#include <vector>

using namespace clang;
using namespace verify;

static bool sameValueType(const VType &L, const VType &R) {
  if (L.Kind != R.Kind)
    return false;
  if (L.Kind != VTypeKind::Int32 && L.Kind != VTypeKind::Int64)
    return true;
  return L.IntMode == R.IntMode && L.IsSigned == R.IsSigned &&
         L.BitWidth == R.BitWidth;
}

static bool isIntegralValueType(const VType &Ty) {
  return Ty.Kind == VTypeKind::Bool || Ty.Kind == VTypeKind::Int32 ||
         Ty.Kind == VTypeKind::Int64;
}

static std::unique_ptr<VExpr> convertValue(std::unique_ptr<VExpr> Value,
                                           const VType &Target) {
  if (!Value || sameValueType(Value->Ty, Target))
    return Value;
  if (Target.IntMode == VIntMode::Machine && Value->K == VExpr::Cast) {
    auto *Cast = static_cast<VCastExpr *>(Value.get());
    if (Cast->Ty.IntMode == VIntMode::Math &&
        sameValueType(Cast->FromTy, Target) &&
        sameValueType(Cast->Inner->Ty, Target))
      return std::move(Cast->Inner);
  }
  if (!isIntegralValueType(Value->Ty) || !isIntegralValueType(Target))
    return Value;
  VType Source = Value->Ty;
  SourceLocation Loc = Value->Loc;
  return std::make_unique<VCastExpr>(std::move(Value), Source, Target, Loc);
}

static std::unique_ptr<VExpr> makeTraceNot(std::unique_ptr<VExpr> E,
                                           SourceLocation Loc) {
  return std::make_unique<VUnaryOpExpr>(VUnaryOp::Not, std::move(E),
                                        VType::makeBool(), Loc);
}

static std::unique_ptr<VExpr> makeTraceAnd(std::unique_ptr<VExpr> L,
                                           std::unique_ptr<VExpr> R,
                                           SourceLocation Loc) {
  return std::make_unique<VBinOpExpr>(VBinOp::And, std::move(L), std::move(R),
                                      VType::makeBool(), Loc);
}

static std::unique_ptr<VExpr> makeTraceOr(std::unique_ptr<VExpr> L,
                                          std::unique_ptr<VExpr> R,
                                          SourceLocation Loc) {
  return std::make_unique<VBinOpExpr>(VBinOp::Or, std::move(L), std::move(R),
                                      VType::makeBool(), Loc);
}

static std::map<std::string, std::unique_ptr<VExpr>>
bindParams(const VFunction &Fn,
           const std::vector<std::unique_ptr<VExpr>> &Args) {
  std::map<std::string, std::unique_ptr<VExpr>> Env;
  for (unsigned I = 0; I < Fn.Params.size() && I < Args.size(); ++I)
    Env[Fn.Params[I].first] =
        convertValue(cloneVExpr(Args[I].get()), Fn.Params[I].second);
  return Env;
}

static std::unique_ptr<VExpr>
envLookup(const std::map<std::string, std::unique_ptr<VExpr>> &Env,
          const std::string &Name, VType Ty, SourceLocation Loc,
          const std::string &ProvenanceVariable) {
  if (auto It = Env.find(Name); It != Env.end())
    return cloneVExpr(It->second.get());
  return std::make_unique<VVarExpr>(Name, Ty, Loc, ProvenanceVariable);
}

class SpecInlinerImpl {
  const FunctionMap &FnMap;
  std::map<std::string, unsigned> Fuel;
  std::set<std::string> Hidden;
  std::set<std::string> Revealed;
  unsigned InlineDepth = 0;
  static constexpr unsigned MaxInlineDepth = 256;

  unsigned fuelFor(const std::string &Name) const {
    if (Hidden.count(Name))
      return 0;
    if (auto It = Fuel.find(Name); It != Fuel.end())
      return It->second;
    if (Revealed.count(Name))
      return 1;
    auto It = FnMap.find(Name);
    if (It != FnMap.end() && It->second->NeedsDecreasesCheck)
      return 0;
    return 1;
  }

  static std::unique_ptr<VExpr> atCallSite(std::unique_ptr<VExpr> Expr,
                                           const VSpecCallExpr &Call) {
    if (Expr) {
      Expr->Loc = Call.Loc;
      Expr->EndLoc = Call.EndLoc;
    }
    return Expr;
  }

  std::unique_ptr<VExpr> opaqueCall(const VSpecCallExpr &C) {
    std::vector<std::unique_ptr<VExpr>> Args;
    Args.reserve(C.Args.size());
    for (const auto &Arg : C.Args)
      Args.push_back(cloneVExpr(Arg.get()));
    return atCallSite(std::make_unique<VSpecCallExpr>(
                          C.Callee, C.CalleeIdentity, std::move(Args), C.Ty,
                          C.Loc, C.ReadsHeap, C.HeapVar),
                      C);
  }

  static void
  recordEvaluation(const VExpr *E, const VExpr *Guard,
                   std::vector<std::unique_ptr<VExpr>> *EvaluationTrace) {
    if (!E || !EvaluationTrace || E->Ty.Kind == VTypeKind::Void)
      return;
    std::unique_ptr<VExpr> Reflexive = std::make_unique<VBinOpExpr>(
        VBinOp::Eq, cloneVExpr(E), cloneVExpr(E), VType::makeBool(), E->Loc);
    if (Guard)
      Reflexive = makeTraceOr(makeTraceNot(cloneVExpr(Guard), E->Loc),
                              std::move(Reflexive), E->Loc);
    EvaluationTrace->push_back(std::move(Reflexive));
  }

  static std::unique_ptr<VExpr>
  attachEvaluationTrace(std::unique_ptr<VExpr> Value,
                        std::vector<std::unique_ptr<VExpr>> EvaluationTrace) {
    if (!Value || EvaluationTrace.empty())
      return Value;
    std::unique_ptr<VExpr> Trace =
        std::make_unique<VLiteralExpr>(true, VType::makeBool(), Value->Loc);
    for (auto &Evaluated : EvaluationTrace)
      Trace = makeTraceAnd(std::move(Trace), std::move(Evaluated), Value->Loc);
    VType Ty = Value->Ty;
    SourceLocation Loc = Value->Loc;
    return std::make_unique<VConditionalExpr>(
        std::move(Trace), cloneVExpr(Value.get()), std::move(Value), Ty, Loc);
  }

public:
  SpecInlinerImpl(const FunctionMap &FnMap,
                  std::map<std::string, unsigned> Fuel,
                  std::set<std::string> Hidden, std::set<std::string> Revealed)
      : FnMap(FnMap), Fuel(std::move(Fuel)), Hidden(std::move(Hidden)),
        Revealed(std::move(Revealed)) {}

  std::unique_ptr<VExpr> inlineExpr(std::unique_ptr<VExpr> E) {
    std::map<std::string, std::unique_ptr<VExpr>> Env;
    return evalExpr(E.get(), Env);
  }

  std::unique_ptr<VExpr> inlineSpecCall(const VSpecCallExpr &C) {
    if (InlineDepth++ >= MaxInlineDepth)
      return opaqueCall(C);
    struct DepthGuard {
      unsigned &D;
      ~DepthGuard() { --D; }
    } Guard{InlineDepth};
    if (Hidden.count(C.CalleeIdentity))
      return opaqueCall(C);
    auto It = FnMap.find(C.CalleeIdentity);
    if (It == FnMap.end() || !It->second->IsSpec || It->second->Uninterpreted)
      return opaqueCall(C);
    const VFunction &Spec = *It->second;
    unsigned F = fuelFor(C.CalleeIdentity);
    if (Spec.NeedsDecreasesCheck) {
      if (F == 0)
        return opaqueCall(C);
      auto Env = bindParams(Spec, C.Args);
      auto OldFuel = Fuel[Spec.Identity];
      Fuel[Spec.Identity] = F > 0 ? F - 1 : 0;
      std::vector<std::unique_ptr<VExpr>> EvaluationTrace;
      auto Out =
          evalBody(Spec.Body, Env,
                   Spec.RequiresCallDefinedness ? &EvaluationTrace : nullptr);
      Fuel[Spec.Identity] = OldFuel;
      if (!Out)
        return opaqueCall(C);
      Out = attachEvaluationTrace(std::move(Out), std::move(EvaluationTrace));
      return atCallSite(convertValue(std::move(Out), C.Ty), C);
    }
    auto Env = bindParams(Spec, C.Args);
    std::vector<std::unique_ptr<VExpr>> EvaluationTrace;
    if (auto Out = evalBody(Spec.Body, Env,
                            Spec.RequiresCallDefinedness ? &EvaluationTrace
                                                         : nullptr)) {
      Out = attachEvaluationTrace(std::move(Out), std::move(EvaluationTrace));
      return atCallSite(convertValue(std::move(Out), C.Ty), C);
    }
    return opaqueCall(C);
  }

  void inlineQuantifiedCalls(std::unique_ptr<VExpr> &E) {
    if (!E)
      return;
    switch (E->K) {
    case VExpr::Forall:
    case VExpr::Exists: {
      auto &Q = static_cast<VQuantifiedExpr &>(*E);
      inlineQuantifiedCalls(Q.Lo);
      inlineQuantifiedCalls(Q.Hi);
      Q.Body = inlineExpr(std::move(Q.Body));
      return;
    }
    case VExpr::BinOp: {
      auto &B = static_cast<VBinOpExpr &>(*E);
      inlineQuantifiedCalls(B.Lhs);
      inlineQuantifiedCalls(B.Rhs);
      return;
    }
    case VExpr::UnaryOp:
      inlineQuantifiedCalls(static_cast<VUnaryOpExpr &>(*E).Operand);
      return;
    case VExpr::Cast:
      inlineQuantifiedCalls(static_cast<VCastExpr &>(*E).Inner);
      return;
    case VExpr::Load: {
      auto &Load = static_cast<VLoadExpr &>(*E);
      inlineQuantifiedCalls(Load.Ptr);
      inlineQuantifiedCalls(Load.AccessCondition);
      return;
    }
    case VExpr::Old:
      inlineQuantifiedCalls(static_cast<VOldExpr &>(*E).Inner);
      return;
    case VExpr::Conditional: {
      auto &C = static_cast<VConditionalExpr &>(*E);
      inlineQuantifiedCalls(C.Cond);
      inlineQuantifiedCalls(C.Then);
      inlineQuantifiedCalls(C.Else);
      return;
    }
    case VExpr::OverflowCheck: {
      auto &O = static_cast<VOverflowCheckExpr &>(*E);
      inlineQuantifiedCalls(O.Lhs);
      inlineQuantifiedCalls(O.Rhs);
      return;
    }
    case VExpr::HeapStore: {
      auto &H = static_cast<VHeapStoreExpr &>(*E);
      inlineQuantifiedCalls(H.Ptr);
      inlineQuantifiedCalls(H.Val);
      return;
    }
    case VExpr::HeapFrame:
      for (auto &[Lo, Hi] : static_cast<VHeapFrameExpr &>(*E).Regions) {
        inlineQuantifiedCalls(Lo);
        inlineQuantifiedCalls(Hi);
      }
      return;
    case VExpr::FieldAccess:
      inlineQuantifiedCalls(static_cast<VFieldAccessExpr &>(*E).Base);
      return;
    case VExpr::SpecCall:
      for (auto &Arg : static_cast<VSpecCallExpr &>(*E).Args)
        inlineQuantifiedCalls(Arg);
      return;
    case VExpr::Literal:
    case VExpr::Var:
    case VExpr::Result:
      return;
    }
  }

  void inlineQuantifiedCalls(std::vector<std::unique_ptr<VStmt>> &Stmts) {
    for (auto &S : Stmts) {
      switch (S->K) {
      case VStmt::Assign:
        inlineQuantifiedCalls(static_cast<VAssignStmt &>(*S).Value);
        break;
      case VStmt::Store: {
        auto &Store = static_cast<VStoreStmt &>(*S);
        inlineQuantifiedCalls(Store.Ptr);
        inlineQuantifiedCalls(Store.Value);
        inlineQuantifiedCalls(Store.AccessCondition);
        break;
      }
      case VStmt::Allocate:
        inlineQuantifiedCalls(static_cast<VAllocateStmt &>(*S).Initializer);
        break;
      case VStmt::EndLifetime:
        break;
      case VStmt::Free:
        inlineQuantifiedCalls(static_cast<VFreeStmt &>(*S).Ptr);
        break;
      case VStmt::If: {
        auto &I = static_cast<VIfStmt &>(*S);
        inlineQuantifiedCalls(I.Cond);
        inlineQuantifiedCalls(I.Then);
        inlineQuantifiedCalls(I.Else);
        break;
      }
      case VStmt::While: {
        auto &W = static_cast<VWhileStmt &>(*S);
        inlineQuantifiedCalls(W.Cond);
        for (auto &Inv : W.Invariants)
          inlineQuantifiedCalls(Inv);
        for (auto &Decrease : W.Decreases)
          inlineQuantifiedCalls(Decrease);
        inlineQuantifiedCalls(W.Body);
        break;
      }
      case VStmt::Call:
        for (auto &Arg : static_cast<VCallStmt &>(*S).Args)
          inlineQuantifiedCalls(Arg);
        break;
      case VStmt::Assert:
        inlineQuantifiedCalls(static_cast<VAssertStmt &>(*S).Cond);
        break;
      case VStmt::Assume:
        inlineQuantifiedCalls(static_cast<VAssumeStmt &>(*S).Cond);
        break;
      case VStmt::Return:
        inlineQuantifiedCalls(static_cast<VReturnStmt &>(*S).Value);
        break;
      case VStmt::Seq:
        inlineQuantifiedCalls(static_cast<VSeqStmt &>(*S).Stmts);
        break;
      case VStmt::GhostBlock:
        inlineQuantifiedCalls(static_cast<VGhostBlockStmt &>(*S).Body);
        break;
      case VStmt::ContractAssert:
        inlineQuantifiedCalls(static_cast<VContractAssertStmt &>(*S).Cond);
        break;
      case VStmt::Havoc:
      case VStmt::RevealWithFuel:
      case VStmt::HideSpec:
      case VStmt::RevealSpec:
      case VStmt::Break:
      case VStmt::Continue:
        break;
      }
    }
  }

  void inlineDefinednessCalls(std::unique_ptr<VExpr> &E,
                              bool InsideQuantifier = false) {
    if (!E)
      return;
    if (E->K == VExpr::SpecCall) {
      auto &Call = static_cast<VSpecCallExpr &>(*E);
      auto It = FnMap.find(Call.CalleeIdentity);
      const bool CrossesIntegerMode = It != FnMap.end() &&
                                      (Call.Ty.Kind == VTypeKind::Int32 ||
                                       Call.Ty.Kind == VTypeKind::Int64) &&
                                      Call.Ty.IntMode != It->second->IntMode &&
                                      !It->second->NeedsDecreasesCheck;
      // Keep ordinary scalar calls local, but leave quantified calls axiomatic:
      // mixed Int/BitVec conversions under a quantifier are much harder for Z3.
      const bool InlineNonrecursiveSpec =
          !InsideQuantifier && It != FnMap.end() && It->second->IsSpec &&
          !It->second->NeedsDecreasesCheck;
      if (It != FnMap.end() && (It->second->RequiresCallDefinedness ||
                                CrossesIntegerMode || InlineNonrecursiveSpec)) {
        E = inlineExpr(std::move(E));
        return;
      }
      for (auto &Arg : Call.Args)
        inlineDefinednessCalls(Arg, InsideQuantifier);
      return;
    }
    switch (E->K) {
    case VExpr::BinOp: {
      auto &B = static_cast<VBinOpExpr &>(*E);
      inlineDefinednessCalls(B.Lhs, InsideQuantifier);
      inlineDefinednessCalls(B.Rhs, InsideQuantifier);
      return;
    }
    case VExpr::UnaryOp:
      inlineDefinednessCalls(static_cast<VUnaryOpExpr &>(*E).Operand,
                             InsideQuantifier);
      return;
    case VExpr::Cast:
      inlineDefinednessCalls(static_cast<VCastExpr &>(*E).Inner,
                             InsideQuantifier);
      return;
    case VExpr::Load: {
      auto &Load = static_cast<VLoadExpr &>(*E);
      inlineDefinednessCalls(Load.Ptr, InsideQuantifier);
      inlineDefinednessCalls(Load.AccessCondition, InsideQuantifier);
      return;
    }
    case VExpr::Old:
      inlineDefinednessCalls(static_cast<VOldExpr &>(*E).Inner,
                             InsideQuantifier);
      return;
    case VExpr::Conditional: {
      auto &C = static_cast<VConditionalExpr &>(*E);
      inlineDefinednessCalls(C.Cond, InsideQuantifier);
      inlineDefinednessCalls(C.Then, InsideQuantifier);
      inlineDefinednessCalls(C.Else, InsideQuantifier);
      return;
    }
    case VExpr::OverflowCheck: {
      auto &O = static_cast<VOverflowCheckExpr &>(*E);
      inlineDefinednessCalls(O.Lhs, InsideQuantifier);
      inlineDefinednessCalls(O.Rhs, InsideQuantifier);
      return;
    }
    case VExpr::Forall:
    case VExpr::Exists: {
      auto &Q = static_cast<VQuantifiedExpr &>(*E);
      inlineDefinednessCalls(Q.Lo, InsideQuantifier);
      inlineDefinednessCalls(Q.Hi, InsideQuantifier);
      inlineDefinednessCalls(Q.Body, true);
      return;
    }
    case VExpr::HeapStore: {
      auto &H = static_cast<VHeapStoreExpr &>(*E);
      inlineDefinednessCalls(H.Ptr, InsideQuantifier);
      inlineDefinednessCalls(H.Val, InsideQuantifier);
      return;
    }
    case VExpr::HeapFrame:
      for (auto &[Lo, Hi] : static_cast<VHeapFrameExpr &>(*E).Regions) {
        inlineDefinednessCalls(Lo, InsideQuantifier);
        inlineDefinednessCalls(Hi, InsideQuantifier);
      }
      return;
    case VExpr::FieldAccess:
      inlineDefinednessCalls(static_cast<VFieldAccessExpr &>(*E).Base,
                             InsideQuantifier);
      return;
    case VExpr::Literal:
    case VExpr::Var:
    case VExpr::Result:
    case VExpr::SpecCall:
      return;
    }
  }

  void inlineDefinednessCalls(std::vector<std::unique_ptr<VStmt>> &Stmts) {
    for (auto &S : Stmts) {
      switch (S->K) {
      case VStmt::Assign:
        inlineDefinednessCalls(static_cast<VAssignStmt &>(*S).Value);
        break;
      case VStmt::Store: {
        auto &Store = static_cast<VStoreStmt &>(*S);
        inlineDefinednessCalls(Store.Ptr);
        inlineDefinednessCalls(Store.Value);
        inlineDefinednessCalls(Store.AccessCondition);
        break;
      }
      case VStmt::Allocate:
        inlineDefinednessCalls(static_cast<VAllocateStmt &>(*S).Initializer);
        break;
      case VStmt::EndLifetime:
        break;
      case VStmt::Free:
        inlineDefinednessCalls(static_cast<VFreeStmt &>(*S).Ptr);
        break;
      case VStmt::If: {
        auto &I = static_cast<VIfStmt &>(*S);
        inlineDefinednessCalls(I.Cond);
        inlineDefinednessCalls(I.Then);
        inlineDefinednessCalls(I.Else);
        break;
      }
      case VStmt::While: {
        auto &W = static_cast<VWhileStmt &>(*S);
        inlineDefinednessCalls(W.Cond);
        for (auto &Inv : W.Invariants)
          inlineDefinednessCalls(Inv);
        for (auto &Decrease : W.Decreases)
          inlineDefinednessCalls(Decrease);
        inlineDefinednessCalls(W.Body);
        break;
      }
      case VStmt::Call:
        for (auto &Arg : static_cast<VCallStmt &>(*S).Args)
          inlineDefinednessCalls(Arg);
        break;
      case VStmt::Assert:
        inlineDefinednessCalls(static_cast<VAssertStmt &>(*S).Cond);
        break;
      case VStmt::Assume:
        inlineDefinednessCalls(static_cast<VAssumeStmt &>(*S).Cond);
        break;
      case VStmt::Return:
        inlineDefinednessCalls(static_cast<VReturnStmt &>(*S).Value);
        break;
      case VStmt::Seq:
        inlineDefinednessCalls(static_cast<VSeqStmt &>(*S).Stmts);
        break;
      case VStmt::GhostBlock:
        inlineDefinednessCalls(static_cast<VGhostBlockStmt &>(*S).Body);
        break;
      case VStmt::ContractAssert:
        inlineDefinednessCalls(static_cast<VContractAssertStmt &>(*S).Cond);
        break;
      case VStmt::Havoc:
      case VStmt::RevealWithFuel:
      case VStmt::HideSpec:
      case VStmt::RevealSpec:
      case VStmt::Break:
      case VStmt::Continue:
        break;
      }
    }
  }

  std::unique_ptr<VExpr>
  evalExpr(const VExpr *E,
           const std::map<std::string, std::unique_ptr<VExpr>> &Env) {
    auto Result = evalExprImpl(E, Env);
    if (Result && E)
      Result->EndLoc = E->EndLoc;
    return Result;
  }

  std::unique_ptr<VExpr>
  evalExprImpl(const VExpr *E,
               const std::map<std::string, std::unique_ptr<VExpr>> &Env) {
    if (!E)
      return nullptr;
    switch (E->K) {
    case VExpr::Literal:
      return cloneVExpr(E);
    case VExpr::Var: {
      const auto *V = static_cast<const VVarExpr *>(E);
      return envLookup(Env, V->Name, E->Ty, E->Loc, V->ProvenanceVariable);
    }
    case VExpr::BinOp: {
      const auto *B = static_cast<const VBinOpExpr *>(E);
      auto L = evalExpr(B->Lhs.get(), Env);
      auto R = evalExpr(B->Rhs.get(), Env);
      if (!L || !R)
        return nullptr;
      return std::make_unique<VBinOpExpr>(B->Op, std::move(L), std::move(R),
                                          B->Ty, B->Loc);
    }
    case VExpr::UnaryOp: {
      const auto *U = static_cast<const VUnaryOpExpr *>(E);
      auto O = evalExpr(U->Operand.get(), Env);
      if (!O)
        return nullptr;
      return std::make_unique<VUnaryOpExpr>(U->Op, std::move(O), U->Ty, U->Loc);
    }
    case VExpr::Cast: {
      const auto *C = static_cast<const VCastExpr *>(E);
      auto I = evalExpr(C->Inner.get(), Env);
      if (!I)
        return nullptr;
      return std::make_unique<VCastExpr>(std::move(I), C->FromTy, C->Ty,
                                         C->Loc, C->IsTrigger);
    }
    case VExpr::Conditional: {
      const auto *C = static_cast<const VConditionalExpr *>(E);
      auto Cond = evalExpr(C->Cond.get(), Env);
      auto T = evalExpr(C->Then.get(), Env);
      auto F = evalExpr(C->Else.get(), Env);
      if (!Cond || !T || !F)
        return nullptr;
      return std::make_unique<VConditionalExpr>(std::move(Cond), std::move(T),
                                                std::move(F), C->Ty, C->Loc);
    }
    case VExpr::OverflowCheck: {
      const auto *O = static_cast<const VOverflowCheckExpr *>(E);
      auto Lhs = evalExpr(O->Lhs.get(), Env);
      auto Rhs = O->Rhs ? evalExpr(O->Rhs.get(), Env) : nullptr;
      if (!Lhs || (O->Rhs && !Rhs))
        return nullptr;
      return std::make_unique<VOverflowCheckExpr>(O->Op, std::move(Lhs),
                                                  std::move(Rhs), O->Loc);
    }
    case VExpr::SpecCall: {
      const auto *C = static_cast<const VSpecCallExpr *>(E);
      std::vector<std::unique_ptr<VExpr>> Args;
      Args.reserve(C->Args.size());
      for (const auto &Arg : C->Args) {
        auto Evaluated = evalExpr(Arg.get(), Env);
        if (!Evaluated)
          return nullptr;
        Args.push_back(std::move(Evaluated));
      }
      VSpecCallExpr EvaluatedCall(C->Callee, C->CalleeIdentity, std::move(Args),
                                  C->Ty, C->Loc, C->ReadsHeap, C->HeapVar);
      return inlineSpecCall(EvaluatedCall);
    }
    case VExpr::Forall:
    case VExpr::Exists: {
      const auto *Q = static_cast<const VQuantifiedExpr *>(E);
      auto Lo = Q->Lo ? evalExpr(Q->Lo.get(), Env) : nullptr;
      auto Hi = Q->Hi ? evalExpr(Q->Hi.get(), Env) : nullptr;
      auto BodyEnv = cloneEnv(Env);
      BodyEnv.erase(Q->Binder);
      auto Body = evalExpr(Q->Body.get(), BodyEnv);
      if ((Q->Lo && (!Lo || !Hi)) || !Body)
        return nullptr;
      if (E->K == VExpr::Forall)
        return std::unique_ptr<VExpr>(std::make_unique<VForallExpr>(
            Q->Binder, std::move(Lo), std::move(Hi), std::move(Body), Q->Loc,
            Q->BinderType));
      return std::unique_ptr<VExpr>(std::make_unique<VExistsExpr>(
          Q->Binder, std::move(Lo), std::move(Hi), std::move(Body), Q->Loc,
          Q->BinderType));
    }
    case VExpr::Load: {
      const auto *L = static_cast<const VLoadExpr *>(E);
      auto Ptr = evalExpr(L->Ptr.get(), Env);
      if (!Ptr)
        return nullptr;
      std::unique_ptr<VExpr> Condition;
      if (L->AccessCondition) {
        Condition = evalExpr(L->AccessCondition.get(), Env);
        if (!Condition)
          return nullptr;
      }
      return std::make_unique<VLoadExpr>(std::move(Ptr), L->Ty, L->Loc,
                                         L->HeapVar, std::move(Condition));
    }
    case VExpr::FieldAccess: {
      const auto *F = static_cast<const VFieldAccessExpr *>(E);
      if (F->Base->K == VExpr::Var) {
        const std::string Flattened =
            static_cast<const VVarExpr *>(F->Base.get())->Name + "." + F->Field;
        if (auto It = Env.find(Flattened); It != Env.end())
          return cloneVExpr(It->second.get());
      }
      auto Base = evalExpr(F->Base.get(), Env);
      if (!Base)
        return nullptr;
      return std::make_unique<VFieldAccessExpr>(std::move(Base), F->Field,
                                                F->Ty, F->Loc);
    }
    // Caller-context call arguments contain these.
    case VExpr::Result:
      return cloneVExpr(E);
    case VExpr::Old: {
      const auto *O = static_cast<const VOldExpr *>(E);
      auto Inner = evalExpr(O->Inner.get(), Env);
      if (!Inner)
        return nullptr;
      return std::make_unique<VOldExpr>(std::move(Inner), O->Ty, O->Loc);
    }
    case VExpr::HeapStore: {
      const auto *H = static_cast<const VHeapStoreExpr *>(E);
      auto Ptr = evalExpr(H->Ptr.get(), Env);
      auto Val = evalExpr(H->Val.get(), Env);
      if (!Ptr || !Val)
        return nullptr;
      return std::make_unique<VHeapStoreExpr>(
          H->HeapBefore, H->HeapAfter, std::move(Ptr), std::move(Val), H->Loc);
    }
    case VExpr::HeapFrame:
      return nullptr;
    }
    return nullptr;
  }

  std::unique_ptr<VExpr>
  evalBodySeq(const std::vector<std::unique_ptr<VStmt>> &Body,
              std::map<std::string, std::unique_ptr<VExpr>> &Env, unsigned Idx,
              std::vector<std::unique_ptr<VExpr>> *EvaluationTrace,
              const VExpr *Guard) {
    if (Idx >= Body.size())
      return nullptr;
    const VStmt &S = *Body[Idx];
    switch (S.K) {
    case VStmt::Assign: {
      const auto &A = static_cast<const VAssignStmt &>(S);
      auto Value = evalExpr(A.Value.get(), Env);
      if (!Value)
        return nullptr;
      recordEvaluation(Value.get(), Guard, EvaluationTrace);
      Env[A.Target] = std::move(Value);
      return evalBodySeq(Body, Env, Idx + 1, EvaluationTrace, Guard);
    }
    case VStmt::Return: {
      const auto &R = static_cast<const VReturnStmt &>(S);
      auto Value = evalExpr(R.Value.get(), Env);
      recordEvaluation(Value.get(), Guard, EvaluationTrace);
      return Value;
    }
    case VStmt::If: {
      const auto &I = static_cast<const VIfStmt &>(S);
      auto Cond = evalExpr(I.Cond.get(), Env);
      if (!Cond)
        return nullptr;
      recordEvaluation(Cond.get(), Guard, EvaluationTrace);
      auto ThenGuard =
          makeTraceAnd(cloneVExpr(Guard), cloneVExpr(Cond.get()), I.Loc);
      auto ElseGuard =
          makeTraceAnd(cloneVExpr(Guard),
                       makeTraceNot(cloneVExpr(Cond.get()), I.Loc), I.Loc);
      if (I.Else.empty()) {
        auto ThenEnv = cloneEnv(Env);
        auto ThenVal =
            evalBody(I.Then, ThenEnv, EvaluationTrace, ThenGuard.get());
        if (ThenVal) {
          auto Rest =
              evalBodySeq(Body, Env, Idx + 1, EvaluationTrace, ElseGuard.get());
          if (!Rest)
            return nullptr;
          VType ResultTy = ThenVal->Ty;
          return std::make_unique<VConditionalExpr>(
              std::move(Cond), std::move(ThenVal), std::move(Rest), ResultTy,
              I.Loc);
        }
        auto ElseEnv = cloneEnv(Env);
        mergeEnvironments(Env, ThenEnv, ElseEnv, Cond.get(), I.Loc);
        return evalBodySeq(Body, Env, Idx + 1, EvaluationTrace, Guard);
      }
      auto ThenEnv = cloneEnv(Env);
      auto ElseEnv = cloneEnv(Env);
      auto ThenVal =
          evalBody(I.Then, ThenEnv, EvaluationTrace, ThenGuard.get());
      auto ElseVal =
          evalBody(I.Else, ElseEnv, EvaluationTrace, ElseGuard.get());
      if (ThenVal && ElseVal) {
        VType ResultTy = ThenVal->Ty;
        return std::make_unique<VConditionalExpr>(
            std::move(Cond), std::move(ThenVal), std::move(ElseVal), ResultTy,
            I.Loc);
      }
      if (ThenVal) {
        auto Rest = evalBodySeq(Body, ElseEnv, Idx + 1, EvaluationTrace,
                                ElseGuard.get());
        if (!Rest)
          return nullptr;
        VType ResultTy = ThenVal->Ty;
        return std::make_unique<VConditionalExpr>(
            std::move(Cond), std::move(ThenVal), std::move(Rest), ResultTy,
            I.Loc);
      }
      if (ElseVal) {
        auto Rest = evalBodySeq(Body, ThenEnv, Idx + 1, EvaluationTrace,
                                ThenGuard.get());
        if (!Rest)
          return nullptr;
        VType ResultTy = Rest->Ty;
        return std::make_unique<VConditionalExpr>(
            std::move(Cond), std::move(Rest), std::move(ElseVal), ResultTy,
            I.Loc);
      }
      mergeEnvironments(Env, ThenEnv, ElseEnv, Cond.get(), I.Loc);
      return evalBodySeq(Body, Env, Idx + 1, EvaluationTrace, Guard);
    }
    case VStmt::GhostBlock: {
      const auto &G = static_cast<const VGhostBlockStmt &>(S);
      if (auto R = evalBody(G.Body, Env, EvaluationTrace, Guard))
        return R;
      return evalBodySeq(Body, Env, Idx + 1, EvaluationTrace, Guard);
    }
    default:
      return nullptr;
    }
  }

  static std::map<std::string, std::unique_ptr<VExpr>>
  cloneEnv(const std::map<std::string, std::unique_ptr<VExpr>> &Env) {
    std::map<std::string, std::unique_ptr<VExpr>> Out;
    for (const auto &[K, V] : Env)
      Out[K] = cloneVExpr(V.get());
    return Out;
  }

  static void mergeEnvironments(
      std::map<std::string, std::unique_ptr<VExpr>> &Env,
      const std::map<std::string, std::unique_ptr<VExpr>> &ThenEnv,
      const std::map<std::string, std::unique_ptr<VExpr>> &ElseEnv,
      const VExpr *Cond, SourceLocation Loc) {
    std::set<std::string> Names;
    for (const auto &Entry : ThenEnv)
      Names.insert(Entry.first);
    for (const auto &Entry : ElseEnv)
      Names.insert(Entry.first);
    for (const std::string &Name : Names) {
      auto Then = ThenEnv.find(Name);
      auto Else = ElseEnv.find(Name);
      if (Then == ThenEnv.end() || Else == ElseEnv.end())
        continue;
      VType Ty = Then->second->Ty;
      Env[Name] = std::make_unique<VConditionalExpr>(
          cloneVExpr(Cond), cloneVExpr(Then->second.get()),
          cloneVExpr(Else->second.get()), Ty, Loc);
    }
  }

  std::unique_ptr<VExpr>
  evalBody(const std::vector<std::unique_ptr<VStmt>> &Body,
           std::map<std::string, std::unique_ptr<VExpr>> &Env,
           std::vector<std::unique_ptr<VExpr>> *EvaluationTrace = nullptr,
           const VExpr *Guard = nullptr) {
    auto True = std::make_unique<VLiteralExpr>(true, VType::makeBool(),
                                               SourceLocation());
    return evalBodySeq(Body, Env, 0, EvaluationTrace,
                       Guard ? Guard : True.get());
  }

  void inlineStmts(std::vector<std::unique_ptr<VStmt>> &Stmts) {
    for (auto &S : Stmts) {
      switch (S->K) {
      case VStmt::Assign: {
        auto &A = static_cast<VAssignStmt &>(*S);
        A.Value = inlineExpr(std::move(A.Value));
        break;
      }
      case VStmt::Store: {
        auto &Store = static_cast<VStoreStmt &>(*S);
        Store.Ptr = inlineExpr(std::move(Store.Ptr));
        Store.Value = inlineExpr(std::move(Store.Value));
        Store.AccessCondition = inlineExpr(std::move(Store.AccessCondition));
        break;
      }
      case VStmt::Allocate: {
        auto &A = static_cast<VAllocateStmt &>(*S);
        A.Initializer = inlineExpr(std::move(A.Initializer));
        break;
      }
      case VStmt::EndLifetime:
        break;
      case VStmt::Free: {
        auto &F = static_cast<VFreeStmt &>(*S);
        F.Ptr = inlineExpr(std::move(F.Ptr));
        break;
      }
      case VStmt::Return: {
        auto &R = static_cast<VReturnStmt &>(*S);
        R.Value = inlineExpr(std::move(R.Value));
        break;
      }
      case VStmt::If: {
        auto &I = static_cast<VIfStmt &>(*S);
        I.Cond = inlineExpr(std::move(I.Cond));
        inlineStmts(I.Then);
        inlineStmts(I.Else);
        break;
      }
      case VStmt::While: {
        auto &W = static_cast<VWhileStmt &>(*S);
        W.Cond = inlineExpr(std::move(W.Cond));
        for (auto &Inv : W.Invariants)
          Inv = inlineExpr(std::move(Inv));
        for (auto &Decrease : W.Decreases)
          Decrease = inlineExpr(std::move(Decrease));
        inlineStmts(W.Body);
        break;
      }
      case VStmt::ContractAssert: {
        auto &A = static_cast<VContractAssertStmt &>(*S);
        A.Cond = inlineExpr(std::move(A.Cond));
        break;
      }
      case VStmt::Call: {
        auto &Call = static_cast<VCallStmt &>(*S);
        for (auto &Arg : Call.Args)
          Arg = inlineExpr(std::move(Arg));
        break;
      }
      case VStmt::Assert: {
        auto &A = static_cast<VAssertStmt &>(*S);
        A.Cond = inlineExpr(std::move(A.Cond));
        break;
      }
      case VStmt::Assume: {
        auto &A = static_cast<VAssumeStmt &>(*S);
        A.Cond = inlineExpr(std::move(A.Cond));
        break;
      }
      case VStmt::Seq: {
        auto &Seq = static_cast<VSeqStmt &>(*S);
        inlineStmts(Seq.Stmts);
        break;
      }
      case VStmt::GhostBlock: {
        auto &G = static_cast<VGhostBlockStmt &>(*S);
        inlineStmts(G.Body);
        break;
      }
      case VStmt::Havoc:
      case VStmt::RevealWithFuel:
      case VStmt::HideSpec:
      case VStmt::RevealSpec:
        break;
      default:
        break;
      }
    }
  }
};

void SpecInliner::prepareFunctionAxiomatic(VFunction &Fn) {
  for (const auto &KV : Fn.SpecFuel)
    Fuel[KV.first] = std::max(Fuel[KV.first], KV.second);

  SpecInlinerImpl Impl(FnMap, Fuel, Fn.HiddenSpecs, Fn.RevealedSpecs);
  for (auto &Pre : Fn.Preconditions)
    Impl.inlineQuantifiedCalls(Pre);
  for (auto &Post : Fn.Postconditions)
    Impl.inlineQuantifiedCalls(Post);
  for (auto &Rec : Fn.Recommends)
    Impl.inlineQuantifiedCalls(Rec);
  for (auto &Extent : Fn.ValidExtents)
    Impl.inlineQuantifiedCalls(Extent.Length);
  Impl.inlineQuantifiedCalls(Fn.Body);
  for (auto &Pre : Fn.Preconditions)
    Impl.inlineDefinednessCalls(Pre);
  for (auto &Post : Fn.Postconditions)
    Impl.inlineDefinednessCalls(Post);
  for (auto &Rec : Fn.Recommends)
    Impl.inlineDefinednessCalls(Rec);
  for (auto &Extent : Fn.ValidExtents)
    Impl.inlineDefinednessCalls(Extent.Length);
  Impl.inlineDefinednessCalls(Fn.Body);
}

void SpecInliner::prepareFunction(VFunction &Fn) {
  for (const auto &KV : Fn.SpecFuel)
    Fuel[KV.first] = std::max(Fuel[KV.first], KV.second);

  SpecInlinerImpl Impl(FnMap, Fuel, Fn.HiddenSpecs, Fn.RevealedSpecs);
  for (auto &Pre : Fn.Preconditions)
    Pre = Impl.inlineExpr(std::move(Pre));
  for (auto &Post : Fn.Postconditions)
    Post = Impl.inlineExpr(std::move(Post));
  for (auto &Rec : Fn.Recommends)
    Rec = Impl.inlineExpr(std::move(Rec));
  for (auto &Extent : Fn.ValidExtents)
    Extent.Length = Impl.inlineExpr(std::move(Extent.Length));
  Impl.inlineStmts(Fn.Body);
}

std::unique_ptr<VExpr> SpecInliner::unfoldDefinition(
    const VFunction &Spec, const std::map<std::string, unsigned> &FuelMap,
    const std::set<std::string> &Hidden, const std::set<std::string> &Revealed,
    unsigned RootFuel, bool KeepLeaves) const {
  (void)KeepLeaves;
  std::vector<std::unique_ptr<VExpr>> Args;
  for (const auto &P : Spec.Params)
    Args.push_back(
        std::make_unique<VVarExpr>(P.first, P.second, SourceLocation()));
  auto Call = std::make_unique<VSpecCallExpr>(Spec.Name, Spec.Identity,
                                              std::move(Args), Spec.ReturnType,
                                              SourceLocation(), Spec.ReadsHeap);
  std::map<std::string, unsigned> Fuel = FuelMap;
  Fuel[Spec.Identity] = RootFuel;
  SpecInlinerImpl Impl(FnMap, Fuel, Hidden, Revealed);
  return Impl.inlineSpecCall(*Call);
}

std::unique_ptr<VExpr> SpecInliner::inlineExpr(std::unique_ptr<VExpr> E) {
  SpecInlinerImpl Impl(FnMap, Fuel, {}, {});
  return Impl.inlineExpr(std::move(E));
}

void verify::collectSpecCalls(const VExpr *E,
                              std::vector<const VSpecCallExpr *> &Out) {
  if (!E)
    return;
  switch (E->K) {
  case VExpr::SpecCall: {
    const auto *C = static_cast<const VSpecCallExpr *>(E);
    Out.push_back(C);
    for (const auto &Arg : C->Args)
      collectSpecCalls(Arg.get(), Out);
    return;
  }
  case VExpr::BinOp: {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    collectSpecCalls(B->Lhs.get(), Out);
    collectSpecCalls(B->Rhs.get(), Out);
    return;
  }
  case VExpr::UnaryOp:
    collectSpecCalls(static_cast<const VUnaryOpExpr *>(E)->Operand.get(), Out);
    return;
  case VExpr::Cast:
    collectSpecCalls(static_cast<const VCastExpr *>(E)->Inner.get(), Out);
    return;
  case VExpr::Load: {
    const auto *Load = static_cast<const VLoadExpr *>(E);
    collectSpecCalls(Load->Ptr.get(), Out);
    collectSpecCalls(Load->AccessCondition.get(), Out);
    return;
  }
  case VExpr::Old:
    collectSpecCalls(static_cast<const VOldExpr *>(E)->Inner.get(), Out);
    return;
  case VExpr::Conditional: {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    collectSpecCalls(C->Cond.get(), Out);
    collectSpecCalls(C->Then.get(), Out);
    collectSpecCalls(C->Else.get(), Out);
    return;
  }
  case VExpr::OverflowCheck: {
    const auto *O = static_cast<const VOverflowCheckExpr *>(E);
    collectSpecCalls(O->Lhs.get(), Out);
    collectSpecCalls(O->Rhs.get(), Out);
    return;
  }
  case VExpr::Forall:
  case VExpr::Exists: {
    const auto *Q = static_cast<const VQuantifiedExpr *>(E);
    collectSpecCalls(Q->Lo.get(), Out);
    collectSpecCalls(Q->Hi.get(), Out);
    collectSpecCalls(Q->Body.get(), Out);
    return;
  }
  case VExpr::HeapStore: {
    const auto *H = static_cast<const VHeapStoreExpr *>(E);
    collectSpecCalls(H->Ptr.get(), Out);
    collectSpecCalls(H->Val.get(), Out);
    return;
  }
  case VExpr::HeapFrame:
    for (const auto &[Lo, Hi] : static_cast<const VHeapFrameExpr *>(E)->Regions) {
      collectSpecCalls(Lo.get(), Out);
      collectSpecCalls(Hi.get(), Out);
    }
    return;
  case VExpr::FieldAccess:
    collectSpecCalls(static_cast<const VFieldAccessExpr *>(E)->Base.get(), Out);
    return;
  case VExpr::Literal:
  case VExpr::Var:
  case VExpr::Result:
    return;
  }
}

static void
collectSpecCallsInStmts(const std::vector<std::unique_ptr<VStmt>> &Stmts,
                        std::vector<const VSpecCallExpr *> &Out) {
  for (const auto &S : Stmts) {
    switch (S->K) {
    case VStmt::Assign:
      collectSpecCalls(static_cast<const VAssignStmt &>(*S).Value.get(), Out);
      break;
    case VStmt::Store: {
      const auto &Store = static_cast<const VStoreStmt &>(*S);
      collectSpecCalls(Store.Ptr.get(), Out);
      collectSpecCalls(Store.Value.get(), Out);
      collectSpecCalls(Store.AccessCondition.get(), Out);
      break;
    }
    case VStmt::Allocate:
      collectSpecCalls(static_cast<const VAllocateStmt &>(*S).Initializer.get(),
                       Out);
      break;
    case VStmt::EndLifetime:
      break;
    case VStmt::Free:
      collectSpecCalls(static_cast<const VFreeStmt &>(*S).Ptr.get(), Out);
      break;
    case VStmt::If: {
      const auto &I = static_cast<const VIfStmt &>(*S);
      collectSpecCalls(I.Cond.get(), Out);
      collectSpecCallsInStmts(I.Then, Out);
      collectSpecCallsInStmts(I.Else, Out);
      break;
    }
    case VStmt::While: {
      const auto &W = static_cast<const VWhileStmt &>(*S);
      collectSpecCalls(W.Cond.get(), Out);
      for (const auto &Invariant : W.Invariants)
        collectSpecCalls(Invariant.get(), Out);
      for (const auto &Decrease : W.Decreases)
        collectSpecCalls(Decrease.get(), Out);
      collectSpecCallsInStmts(W.Body, Out);
      break;
    }
    case VStmt::Call:
      for (const auto &Arg : static_cast<const VCallStmt &>(*S).Args)
        collectSpecCalls(Arg.get(), Out);
      break;
    case VStmt::Assert:
      collectSpecCalls(static_cast<const VAssertStmt &>(*S).Cond.get(), Out);
      break;
    case VStmt::Assume:
      collectSpecCalls(static_cast<const VAssumeStmt &>(*S).Cond.get(), Out);
      break;
    case VStmt::Return:
      collectSpecCalls(static_cast<const VReturnStmt &>(*S).Value.get(), Out);
      break;
    case VStmt::Seq:
      collectSpecCallsInStmts(static_cast<const VSeqStmt &>(*S).Stmts, Out);
      break;
    case VStmt::GhostBlock:
      collectSpecCallsInStmts(static_cast<const VGhostBlockStmt &>(*S).Body,
                              Out);
      break;
    case VStmt::ContractAssert:
      collectSpecCalls(static_cast<const VContractAssertStmt &>(*S).Cond.get(),
                       Out);
      break;
    case VStmt::Havoc:
    case VStmt::RevealWithFuel:
    case VStmt::HideSpec:
    case VStmt::RevealSpec:
    case VStmt::Break:
    case VStmt::Continue:
      break;
    }
  }
}

void verify::collectSpecCallsInFunction(
    const VFunction &Fn, std::vector<const VSpecCallExpr *> &Out) {
  for (const auto &P : Fn.Preconditions)
    collectSpecCalls(P.get(), Out);
  for (const auto &P : Fn.Postconditions)
    collectSpecCalls(P.get(), Out);
  for (const auto &Decrease : Fn.Decreases)
    collectSpecCalls(Decrease.get(), Out);
  for (const auto &Extent : Fn.ValidExtents)
    collectSpecCalls(Extent.Length.get(), Out);
  collectSpecCallsInStmts(Fn.Body, Out);
}

std::unique_ptr<VExpr> verify::substParamsInExpr(
    const VExpr *E, const std::map<std::string, std::unique_ptr<VExpr>> &Map) {
  if (!E)
    return nullptr;
  switch (E->K) {
  case VExpr::Var: {
    const auto *V = static_cast<const VVarExpr *>(E);
    if (auto It = Map.find(V->Name); It != Map.end())
      return cloneVExpr(It->second.get());
    return cloneVExpr(E);
  }
  case VExpr::BinOp: {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    return std::make_unique<VBinOpExpr>(
        B->Op, substParamsInExpr(B->Lhs.get(), Map),
        substParamsInExpr(B->Rhs.get(), Map), B->Ty, B->Loc);
  }
  case VExpr::UnaryOp: {
    const auto *U = static_cast<const VUnaryOpExpr *>(E);
    return std::make_unique<VUnaryOpExpr>(
        U->Op, substParamsInExpr(U->Operand.get(), Map), U->Ty, U->Loc,
        U->AllocationHeapVar, U->LivenessHeapVar, U->InitializationHeapVar);
  }
  case VExpr::Cast: {
    const auto *C = static_cast<const VCastExpr *>(E);
    return std::make_unique<VCastExpr>(substParamsInExpr(C->Inner.get(), Map),
                                       C->FromTy, C->Ty, C->Loc, C->IsTrigger);
  }
  case VExpr::Load: {
    const auto *L = static_cast<const VLoadExpr *>(E);
    return std::make_unique<VLoadExpr>(
        substParamsInExpr(L->Ptr.get(), Map), L->Ty, L->Loc, L->HeapVar,
        substParamsInExpr(L->AccessCondition.get(), Map));
  }
  case VExpr::Old: {
    const auto *O = static_cast<const VOldExpr *>(E);
    return std::make_unique<VOldExpr>(substParamsInExpr(O->Inner.get(), Map),
                                      O->Ty, O->Loc);
  }
  case VExpr::Conditional: {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    return std::make_unique<VConditionalExpr>(
        substParamsInExpr(C->Cond.get(), Map),
        substParamsInExpr(C->Then.get(), Map),
        substParamsInExpr(C->Else.get(), Map), C->Ty, C->Loc);
  }
  case VExpr::Forall:
  case VExpr::Exists: {
    const auto *Q = static_cast<const VQuantifiedExpr *>(E);
    std::map<std::string, std::unique_ptr<VExpr>> BodyMap;
    for (const auto &[Name, Value] : Map)
      if (Name != Q->Binder)
        BodyMap[Name] = cloneVExpr(Value.get());
    auto Lo = substParamsInExpr(Q->Lo.get(), Map);
    auto Hi = substParamsInExpr(Q->Hi.get(), Map);
    auto Body = substParamsInExpr(Q->Body.get(), BodyMap);
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
        H->HeapBefore, H->HeapAfter, substParamsInExpr(H->Ptr.get(), Map),
        substParamsInExpr(H->Val.get(), Map), H->Loc);
  }
  case VExpr::HeapFrame: {
    const auto *H = static_cast<const VHeapFrameExpr *>(E);
    std::vector<std::pair<std::unique_ptr<VExpr>, std::unique_ptr<VExpr>>>
        Regions;
    for (const auto &[Lo, Hi] : H->Regions)
      Regions.emplace_back(substParamsInExpr(Lo.get(), Map),
                           substParamsInExpr(Hi.get(), Map));
    return std::make_unique<VHeapFrameExpr>(H->HeapBefore, H->HeapAfter,
                                            std::move(Regions), H->Loc);
  }
  case VExpr::FieldAccess: {
    const auto *F = static_cast<const VFieldAccessExpr *>(E);
    return std::make_unique<VFieldAccessExpr>(
        substParamsInExpr(F->Base.get(), Map), F->Field, F->Ty, F->Loc);
  }
  case VExpr::SpecCall: {
    const auto *C = static_cast<const VSpecCallExpr *>(E);
    std::vector<std::unique_ptr<VExpr>> Args;
    for (const auto &Arg : C->Args)
      Args.push_back(substParamsInExpr(Arg.get(), Map));
    return std::make_unique<VSpecCallExpr>(C->Callee, C->CalleeIdentity,
                                           std::move(Args), C->Ty, C->Loc,
                                           C->ReadsHeap, C->HeapVar);
  }
  case VExpr::OverflowCheck: {
    const auto *O = static_cast<const VOverflowCheckExpr *>(E);
    return std::make_unique<VOverflowCheckExpr>(
        O->Op, substParamsInExpr(O->Lhs.get(), Map),
        O->Rhs ? substParamsInExpr(O->Rhs.get(), Map) : nullptr, O->Loc);
  }
  case VExpr::Result:
    if (auto It = Map.find(ResultKey); It != Map.end())
      return cloneVExpr(It->second.get());
    return cloneVExpr(E);
  case VExpr::Literal:
    return cloneVExpr(E);
  }
  return nullptr;
}

static std::map<std::string, std::unique_ptr<VExpr>>
cloneExprMap(const std::map<std::string, std::unique_ptr<VExpr>> &Map) {
  std::map<std::string, std::unique_ptr<VExpr>> Out;
  for (const auto &[Name, Value] : Map)
    Out[Name] = cloneVExpr(Value.get());
  return Out;
}

static std::unique_ptr<VExpr> makeDecreaseNot(std::unique_ptr<VExpr> E,
                                              SourceLocation Loc) {
  return std::make_unique<VUnaryOpExpr>(VUnaryOp::Not, std::move(E),
                                        VType::makeBool(), Loc);
}

static std::unique_ptr<VExpr> makeDecreaseAnd(std::unique_ptr<VExpr> L,
                                              std::unique_ptr<VExpr> R,
                                              SourceLocation Loc) {
  return std::make_unique<VBinOpExpr>(VBinOp::And, std::move(L), std::move(R),
                                      VType::makeBool(), Loc);
}

struct RecursiveExecSite {
  const VCallStmt *Call = nullptr;
  /// A function of the caller's recursion cycle, the caller included.
  const VFunction *Callee = nullptr;
  std::map<std::string, std::unique_ptr<VExpr>> Args;
  std::unique_ptr<VExpr> Guard;
};

struct DecreaseState {
  std::map<std::string, std::unique_ptr<VExpr>> Env;
  std::unique_ptr<VExpr> Guard;
};

static std::vector<DecreaseState>
collectRecursiveCalls(const std::vector<std::unique_ptr<VStmt>> &Stmts,
                      const VFunction &Self, const FunctionMap &FnMap,
                      std::vector<RecursiveExecSite> &Sites,
                      std::vector<DecreaseState> States, bool &Unsupported) {
  for (const auto &S : Stmts) {
    std::vector<DecreaseState> NextStates;
    for (DecreaseState &State : States) {
      switch (S->K) {
      case VStmt::Assign: {
        const auto &A = static_cast<const VAssignStmt &>(*S);
        State.Env[A.Target] = substParamsInExpr(A.Value.get(), State.Env);
        NextStates.push_back(std::move(State));
        break;
      }
      case VStmt::Store:
        Unsupported = true;
        NextStates.push_back(std::move(State));
        break;
      case VStmt::Allocate:
      case VStmt::Free:
        Unsupported = true;
        NextStates.push_back(std::move(State));
        break;
      case VStmt::EndLifetime:
        NextStates.push_back(std::move(State));
        break;
      case VStmt::Call: {
        const auto &C = static_cast<const VCallStmt &>(*S);
        auto It = FnMap.find(C.CalleeIdentity);
        if (It != FnMap.end() &&
            (C.CalleeIdentity == Self.Identity ||
             Self.RecursionGroup.count(C.CalleeIdentity))) {
          RecursiveExecSite Site;
          Site.Call = &C;
          Site.Callee = It->second;
          for (unsigned I = 0;
               I < It->second->Params.size() && I < C.Args.size(); ++I)
            Site.Args[It->second->Params[I].first] =
                substParamsInExpr(C.Args[I].get(), State.Env);
          Site.Guard = cloneVExpr(State.Guard.get());
          Sites.push_back(std::move(Site));
        }
        if (It != FnMap.end() && C.CalleeIdentity != Self.Identity &&
            !It->second->IsProof) {
          bool HasImplicitHeapEffect = It->second->Modifies.empty();
          if (HasImplicitHeapEffect) {
            HasImplicitHeapEffect = false;
            for (const auto &Param : It->second->Params)
              HasImplicitHeapEffect |= Param.second.Kind == VTypeKind::Ptr;
          }
          Unsupported |= !It->second->Modifies.empty() || HasImplicitHeapEffect;
        }
        if (!C.ResultTarget.empty() && It != FnMap.end())
          State.Env[C.ResultTarget] = std::make_unique<VVarExpr>(
              C.ResultTarget, It->second->ReturnType, C.Loc);
        NextStates.push_back(std::move(State));
        break;
      }
      case VStmt::If: {
        const auto &I = static_cast<const VIfStmt &>(*S);
        auto Cond = substParamsInExpr(I.Cond.get(), State.Env);
        DecreaseState ThenState{cloneExprMap(State.Env),
                                makeDecreaseAnd(cloneVExpr(State.Guard.get()),
                                                cloneVExpr(Cond.get()), I.Loc)};
        std::vector<DecreaseState> ThenStates;
        ThenStates.push_back(std::move(ThenState));
        ThenStates = collectRecursiveCalls(I.Then, Self, FnMap, Sites,
                                           std::move(ThenStates), Unsupported);
        NextStates.insert(NextStates.end(),
                          std::make_move_iterator(ThenStates.begin()),
                          std::make_move_iterator(ThenStates.end()));

        DecreaseState ElseState{
            std::move(State.Env),
            makeDecreaseAnd(std::move(State.Guard),
                            makeDecreaseNot(std::move(Cond), I.Loc), I.Loc)};
        std::vector<DecreaseState> ElseStates;
        ElseStates.push_back(std::move(ElseState));
        ElseStates = collectRecursiveCalls(I.Else, Self, FnMap, Sites,
                                           std::move(ElseStates), Unsupported);
        NextStates.insert(NextStates.end(),
                          std::make_move_iterator(ElseStates.begin()),
                          std::make_move_iterator(ElseStates.end()));
        break;
      }
      case VStmt::While:
      case VStmt::Break:
      case VStmt::Continue:
        Unsupported = true;
        NextStates.push_back(std::move(State));
        break;
      case VStmt::Assert:
      case VStmt::Assume:
      case VStmt::ContractAssert: {
        const VExpr *Cond =
            S->K == VStmt::Assert
                ? static_cast<const VAssertStmt &>(*S).Cond.get()
            : S->K == VStmt::Assume
                ? static_cast<const VAssumeStmt &>(*S).Cond.get()
                : static_cast<const VContractAssertStmt &>(*S).Cond.get();
        State.Guard = makeDecreaseAnd(
            std::move(State.Guard), substParamsInExpr(Cond, State.Env), S->Loc);
        NextStates.push_back(std::move(State));
        break;
      }
      case VStmt::Return:
        break;
      case VStmt::Seq: {
        std::vector<DecreaseState> InnerStates;
        InnerStates.push_back(std::move(State));
        InnerStates = collectRecursiveCalls(
            static_cast<const VSeqStmt &>(*S).Stmts, Self, FnMap, Sites,
            std::move(InnerStates), Unsupported);
        NextStates.insert(NextStates.end(),
                          std::make_move_iterator(InnerStates.begin()),
                          std::make_move_iterator(InnerStates.end()));
        break;
      }
      case VStmt::GhostBlock: {
        std::vector<DecreaseState> InnerStates;
        InnerStates.push_back(std::move(State));
        InnerStates = collectRecursiveCalls(
            static_cast<const VGhostBlockStmt &>(*S).Body, Self, FnMap, Sites,
            std::move(InnerStates), Unsupported);
        NextStates.insert(NextStates.end(),
                          std::make_move_iterator(InnerStates.begin()),
                          std::make_move_iterator(InnerStates.end()));
        break;
      }
      case VStmt::Havoc: {
        const auto &H = static_cast<const VHavocStmt &>(*S);
        VType Ty = VType::makeInt32(VIntMode::Machine);
        if (auto It = State.Env.find(H.Target); It != State.Env.end())
          Ty = It->second->Ty;
        State.Env[H.Target] = std::make_unique<VVarExpr>(H.Target, Ty, H.Loc);
        NextStates.push_back(std::move(State));
        break;
      }
      case VStmt::RevealWithFuel:
      case VStmt::HideSpec:
      case VStmt::RevealSpec:
        NextStates.push_back(std::move(State));
        break;
      }
    }
    States = std::move(NextStates);
    if (States.empty())
      break;
  }
  return States;
}

bool verify::functionHasRecursiveSpecCall(const VFunction &Fn,
                                          const FunctionMap &FnMap) {
  std::vector<RecursiveExecSite> Sites;
  DecreaseState Initial;
  for (const auto &Param : Fn.Params)
    Initial.Env[Param.first] =
        std::make_unique<VVarExpr>(Param.first, Param.second, SourceLocation());
  Initial.Guard =
      std::make_unique<VLiteralExpr>(1, VType::makeBool(), SourceLocation());
  std::vector<DecreaseState> States;
  States.push_back(std::move(Initial));
  bool Unsupported = false;
  collectRecursiveCalls(Fn.Body, Fn, FnMap, Sites, std::move(States),
                        Unsupported);
  return !Sites.empty();
}

/// A quantifier enclosing a recursive call: the call happens at every binder
/// value in its range.
struct EnclosingQuantifier {
  std::string Binder;
  VType BinderType;
  std::unique_ptr<VExpr> Lo;
  std::unique_ptr<VExpr> Hi;
};

struct RecursiveSpecSite {
  /// A function of the caller's recursion cycle, the caller included.
  std::string Callee;
  std::vector<std::unique_ptr<VExpr>> Args;
  std::unique_ptr<VExpr> Guard;
  SourceLocation Loc;
  /// Outermost first.
  std::vector<EnclosingQuantifier> Quantifiers;
};

static void collectRecursiveSpecCallsInExpr(
    const VExpr *E, const VFunction &Fn,
    const std::map<std::string, std::unique_ptr<VExpr>> &Env,
    const VExpr *Guard, std::vector<RecursiveSpecSite> &Sites,
    const std::vector<const VQuantifiedExpr *> &Quantifiers,
    bool &Unsupported) {
  if (!E)
    return;
  switch (E->K) {
  case VExpr::SpecCall: {
    const auto *C = static_cast<const VSpecCallExpr *>(E);
    if (C->CalleeIdentity == Fn.Identity ||
        Fn.RecursionGroup.count(C->CalleeIdentity)) {
      RecursiveSpecSite Site;
      Site.Callee = C->CalleeIdentity;
      for (const auto &Arg : C->Args)
        Site.Args.push_back(substParamsInExpr(Arg.get(), Env));
      Site.Guard = cloneVExpr(Guard);
      Site.Loc = C->Loc;
      for (const VQuantifiedExpr *Q : Quantifiers)
        Site.Quantifiers.push_back({Q->Binder, Q->BinderType,
                                    substParamsInExpr(Q->Lo.get(), Env),
                                    substParamsInExpr(Q->Hi.get(), Env)});
      Sites.push_back(std::move(Site));
    }
    for (const auto &A : C->Args)
      collectRecursiveSpecCallsInExpr(A.get(), Fn, Env, Guard, Sites,
                                      Quantifiers, Unsupported);
    return;
  }
  case VExpr::BinOp: {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    collectRecursiveSpecCallsInExpr(B->Lhs.get(), Fn, Env, Guard, Sites,
                                    Quantifiers, Unsupported);
    std::unique_ptr<VExpr> RightGuard = cloneVExpr(Guard);
    if (B->Op == VBinOp::And)
      RightGuard = makeDecreaseAnd(
          std::move(RightGuard), substParamsInExpr(B->Lhs.get(), Env), B->Loc);
    else if (B->Op == VBinOp::Or)
      RightGuard = makeDecreaseAnd(
          std::move(RightGuard),
          makeDecreaseNot(substParamsInExpr(B->Lhs.get(), Env), B->Loc),
          B->Loc);
    collectRecursiveSpecCallsInExpr(B->Rhs.get(), Fn, Env, RightGuard.get(),
                                    Sites, Quantifiers, Unsupported);
    return;
  }
  case VExpr::UnaryOp:
    collectRecursiveSpecCallsInExpr(
        static_cast<const VUnaryOpExpr *>(E)->Operand.get(), Fn, Env, Guard,
        Sites, Quantifiers, Unsupported);
    return;
  case VExpr::Cast:
    collectRecursiveSpecCallsInExpr(
        static_cast<const VCastExpr *>(E)->Inner.get(), Fn, Env, Guard, Sites,
        Quantifiers, Unsupported);
    return;
  case VExpr::Load: {
    const auto *Load = static_cast<const VLoadExpr *>(E);
    collectRecursiveSpecCallsInExpr(Load->Ptr.get(), Fn, Env, Guard, Sites,
                                    Quantifiers, Unsupported);
    collectRecursiveSpecCallsInExpr(Load->AccessCondition.get(), Fn, Env, Guard,
                                    Sites, Quantifiers, Unsupported);
    return;
  }
  case VExpr::Old:
    collectRecursiveSpecCallsInExpr(
        static_cast<const VOldExpr *>(E)->Inner.get(), Fn, Env, Guard, Sites,
        Quantifiers, Unsupported);
    return;
  case VExpr::Conditional: {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    collectRecursiveSpecCallsInExpr(C->Cond.get(), Fn, Env, Guard, Sites,
                                    Quantifiers, Unsupported);
    auto Cond = substParamsInExpr(C->Cond.get(), Env);
    auto ThenGuard =
        makeDecreaseAnd(cloneVExpr(Guard), cloneVExpr(Cond.get()), C->Loc);
    auto ElseGuard = makeDecreaseAnd(
        cloneVExpr(Guard), makeDecreaseNot(std::move(Cond), C->Loc), C->Loc);
    collectRecursiveSpecCallsInExpr(C->Then.get(), Fn, Env, ThenGuard.get(),
                                    Sites, Quantifiers, Unsupported);
    collectRecursiveSpecCallsInExpr(C->Else.get(), Fn, Env, ElseGuard.get(),
                                    Sites, Quantifiers, Unsupported);
    return;
  }
  case VExpr::OverflowCheck: {
    const auto *O = static_cast<const VOverflowCheckExpr *>(E);
    collectRecursiveSpecCallsInExpr(O->Lhs.get(), Fn, Env, Guard, Sites,
                                    Quantifiers, Unsupported);
    collectRecursiveSpecCallsInExpr(O->Rhs.get(), Fn, Env, Guard, Sites,
                                    Quantifiers, Unsupported);
    return;
  }
  case VExpr::Forall:
  case VExpr::Exists: {
    const auto *Q = static_cast<const VQuantifiedExpr *>(E);
    collectRecursiveSpecCallsInExpr(Q->Lo.get(), Fn, Env, Guard, Sites,
                                    Quantifiers, Unsupported);
    collectRecursiveSpecCallsInExpr(Q->Hi.get(), Fn, Env, Guard, Sites,
                                    Quantifiers, Unsupported);
    std::vector<const VQuantifiedExpr *> Inner = Quantifiers;
    Inner.push_back(Q);
    collectRecursiveSpecCallsInExpr(Q->Body.get(), Fn, Env, Guard, Sites, Inner,
                                    Unsupported);
    return;
  }
  case VExpr::HeapStore: {
    const auto *H = static_cast<const VHeapStoreExpr *>(E);
    collectRecursiveSpecCallsInExpr(H->Ptr.get(), Fn, Env, Guard, Sites,
                                    Quantifiers, Unsupported);
    collectRecursiveSpecCallsInExpr(H->Val.get(), Fn, Env, Guard, Sites,
                                    Quantifiers, Unsupported);
    return;
  }
  case VExpr::HeapFrame:
    Unsupported = true;
    return;
  case VExpr::FieldAccess:
    collectRecursiveSpecCallsInExpr(
        static_cast<const VFieldAccessExpr *>(E)->Base.get(), Fn, Env, Guard,
        Sites, Quantifiers, Unsupported);
    return;
  case VExpr::Literal:
  case VExpr::Var:
  case VExpr::Result:
    return;
  }
}

static std::vector<DecreaseState> collectRecursiveSpecCallsInBody(
    const std::vector<std::unique_ptr<VStmt>> &Stmts, const VFunction &Fn,
    std::vector<RecursiveSpecSite> &Sites, std::vector<DecreaseState> States,
    bool &Unsupported) {
  for (const auto &S : Stmts) {
    std::vector<DecreaseState> NextStates;
    for (DecreaseState &State : States) {
      switch (S->K) {
      case VStmt::Assign: {
        const auto &A = static_cast<const VAssignStmt &>(*S);
        collectRecursiveSpecCallsInExpr(A.Value.get(), Fn, State.Env,
                                        State.Guard.get(), Sites, {},
                                        Unsupported);
        State.Env[A.Target] = substParamsInExpr(A.Value.get(), State.Env);
        NextStates.push_back(std::move(State));
        break;
      }
      case VStmt::Return:
        collectRecursiveSpecCallsInExpr(
            static_cast<const VReturnStmt &>(*S).Value.get(), Fn, State.Env,
            State.Guard.get(), Sites, {}, Unsupported);
        break;
      case VStmt::If: {
        const auto &I = static_cast<const VIfStmt &>(*S);
        collectRecursiveSpecCallsInExpr(I.Cond.get(), Fn, State.Env,
                                        State.Guard.get(), Sites, {},
                                        Unsupported);
        auto Cond = substParamsInExpr(I.Cond.get(), State.Env);

        DecreaseState ThenState{cloneExprMap(State.Env),
                                makeDecreaseAnd(cloneVExpr(State.Guard.get()),
                                                cloneVExpr(Cond.get()), I.Loc)};
        std::vector<DecreaseState> ThenStates;
        ThenStates.push_back(std::move(ThenState));
        ThenStates = collectRecursiveSpecCallsInBody(
            I.Then, Fn, Sites, std::move(ThenStates), Unsupported);
        NextStates.insert(NextStates.end(),
                          std::make_move_iterator(ThenStates.begin()),
                          std::make_move_iterator(ThenStates.end()));

        DecreaseState ElseState{
            std::move(State.Env),
            makeDecreaseAnd(std::move(State.Guard),
                            makeDecreaseNot(std::move(Cond), I.Loc), I.Loc)};
        std::vector<DecreaseState> ElseStates;
        ElseStates.push_back(std::move(ElseState));
        ElseStates = collectRecursiveSpecCallsInBody(
            I.Else, Fn, Sites, std::move(ElseStates), Unsupported);
        NextStates.insert(NextStates.end(),
                          std::make_move_iterator(ElseStates.begin()),
                          std::make_move_iterator(ElseStates.end()));
        break;
      }
      default:
        Unsupported = true;
        break;
      }
    }
    States = std::move(NextStates);
    if (States.empty())
      break;
  }
  return States;
}

/// The measure at a call is below the caller's. Only the deciding component
/// has to be bounded below, and only at the caller (ACSL's variant): along an
/// infinite chain the least index that decides infinitely often would
/// decrease forever from nonnegative values, so the relation is well founded.
static std::unique_ptr<VExpr>
lexicographicDecrease(const std::vector<std::unique_ptr<VExpr>> &CalleeDec,
                      const std::vector<std::unique_ptr<VExpr>> &CurrentDec,
                      SourceLocation Loc) {
  std::unique_ptr<VExpr> LexLess =
      std::make_unique<VLiteralExpr>(false, VType::makeBool(), Loc);
  for (size_t J = 0; J < CalleeDec.size(); ++J) {
    std::unique_ptr<VExpr> Disjunct = makeDecreaseAnd(
        std::make_unique<VBinOpExpr>(
            VBinOp::Ge, cloneVExpr(CurrentDec[J].get()),
            std::make_unique<VLiteralExpr>(0, CurrentDec[J]->Ty, Loc),
            VType::makeBool(), Loc),
        std::make_unique<VBinOpExpr>(VBinOp::Lt, cloneVExpr(CalleeDec[J].get()),
                                     cloneVExpr(CurrentDec[J].get()),
                                     VType::makeBool(), Loc),
        Loc);
    for (size_t I = 0; I < J; ++I)
      Disjunct = makeDecreaseAnd(std::make_unique<VBinOpExpr>(
                                     VBinOp::Eq, cloneVExpr(CalleeDec[I].get()),
                                     cloneVExpr(CurrentDec[I].get()),
                                     VType::makeBool(), Loc),
                                 std::move(Disjunct), Loc);
    LexLess = std::make_unique<VBinOpExpr>(VBinOp::Or, std::move(LexLess),
                                           std::move(Disjunct),
                                           VType::makeBool(), Loc);
  }
  return LexLess;
}

static void addSpecPostChecks(PassiveProgram &P, const VFunction &Fn,
                              const FunctionMap &FnMap);

PassiveProgram verify::buildDecreasesChecks(const VFunction &Fn,
                                            const FunctionMap &FnMap) {
  PassiveProgram P;
  P.FunctionName = Fn.Name + ".decreases";
  P.FunctionIdentity = Fn.Identity + "::decreases";
  if (Fn.Decreases.empty())
    return P;
  P.CallerIntMode = Fn.IntMode;
  P.SpecFunctions = FnMap;
  P.SpecFuel = Fn.SpecFuel;
  P.HiddenSpecs = Fn.HiddenSpecs;
  P.RevealedSpecs = Fn.RevealedSpecs;
  if (Fn.IsSpec) {
    // A definition is a fact only once it terminates, so it cannot help
    // prove its own termination, nor can those of its recursion cycle, and it
    // must terminate for every argument.
    P.HiddenSpecs.insert(Fn.Identity);
    P.HiddenSpecs.insert(Fn.RecursionGroup.begin(), Fn.RecursionGroup.end());
  } else {
    for (const auto &Pre : Fn.Preconditions)
      P.EntryAssumes.push_back(cloneAtEntryState(Pre.get()));
  }

  std::vector<RecursiveExecSite> Sites;
  DecreaseState Initial;
  for (const auto &Param : Fn.Params)
    Initial.Env[Param.first] =
        std::make_unique<VVarExpr>(Param.first, Param.second, SourceLocation());
  Initial.Guard =
      std::make_unique<VLiteralExpr>(1, VType::makeBool(), SourceLocation());
  std::vector<DecreaseState> States;
  States.push_back(std::move(Initial));
  bool UnsupportedExecRecursion = false;
  collectRecursiveCalls(Fn.Body, Fn, FnMap, Sites, std::move(States),
                        UnsupportedExecRecursion);

  std::vector<RecursiveSpecSite> SpecSites;
  bool UnsupportedSpecRecursion = false;
  if (Fn.IsSpec) {
    DecreaseState SpecInitial;
    for (const auto &Param : Fn.Params)
      SpecInitial.Env[Param.first] = std::make_unique<VVarExpr>(
          Param.first, Param.second, SourceLocation());
    SpecInitial.Guard =
        std::make_unique<VLiteralExpr>(1, VType::makeBool(), SourceLocation());
    std::vector<DecreaseState> SpecStates;
    SpecStates.push_back(std::move(SpecInitial));
    collectRecursiveSpecCallsInBody(Fn.Body, Fn, SpecSites,
                                    std::move(SpecStates),
                                    UnsupportedSpecRecursion);
  }

  std::map<std::string, std::unique_ptr<VExpr>> EntryEnv;
  for (const auto &P : Fn.Params)
    EntryEnv[P.first] =
        std::make_unique<VVarExpr>(P.first, P.second, SourceLocation());
  std::vector<std::unique_ptr<VExpr>> CurrentDec;
  for (const auto &Decrease : Fn.Decreases)
    CurrentDec.push_back(substParamsInExpr(Decrease.get(), EntryEnv));

  auto AddObligation = [&](const auto &ArgMap, const VExpr *Guard,
                           SourceLocation Loc,
                           const std::vector<EnclosingQuantifier> *Around =
                               nullptr,
                           const VFunction *Callee = nullptr) {
    std::vector<std::unique_ptr<VExpr>> CalleeDec;
    for (const auto &Decrease : (Callee ? *Callee : Fn).Decreases)
      CalleeDec.push_back(substParamsInExpr(Decrease.get(), ArgMap));

    std::unique_ptr<VExpr> Obligation;
    bool Complete = CalleeDec.size() == CurrentDec.size();
    for (const auto &Value : CalleeDec)
      Complete = Complete && Value != nullptr;
    for (const auto &Value : CurrentDec)
      Complete = Complete && Value != nullptr;
    if (!Complete)
      Obligation =
          std::make_unique<VLiteralExpr>(false, VType::makeBool(), Loc);
    else
      Obligation = lexicographicDecrease(CalleeDec, CurrentDec, Loc);
    if (Guard)
      Obligation = std::make_unique<VBinOpExpr>(
          VBinOp::Or, makeDecreaseNot(cloneVExpr(Guard), Loc),
          std::move(Obligation), VType::makeBool(), Loc);
    // A call under a quantifier happens at every binder value in its range.
    if (Around)
      for (auto It = Around->rbegin(); It != Around->rend(); ++It)
        Obligation = std::make_unique<VForallExpr>(
            It->Binder, cloneVExpr(It->Lo.get()), cloneVExpr(It->Hi.get()),
            std::move(Obligation), Loc, It->BinderType);
    Obligation = cloneAtEntryState(Obligation.get());
    auto PS = std::make_unique<PassiveStmt>();
    PS->K = PassiveStmt::Assert;
    PS->ProofKind = ProofObligationKind::Termination;
    PS->Cond = std::move(Obligation);
    P.Stmts.push_back(std::move(PS));
  };

  for (const RecursiveExecSite &Site : Sites)
    AddObligation(Site.Args, Site.Guard.get(),
                  Site.Call ? Site.Call->Loc : Fn.Decreases.front()->Loc,
                  nullptr, Site.Callee);
  for (const RecursiveSpecSite &Site : SpecSites) {
    const VFunction *Callee = &Fn;
    if (Site.Callee != Fn.Identity) {
      auto It = FnMap.find(Site.Callee);
      if (It == FnMap.end()) {
        UnsupportedSpecRecursion = true;
        continue;
      }
      Callee = It->second;
    }
    std::map<std::string, std::unique_ptr<VExpr>> ArgMap;
    for (unsigned I = 0; I < Callee->Params.size() && I < Site.Args.size(); ++I)
      ArgMap[Callee->Params[I].first] = cloneVExpr(Site.Args[I].get());
    AddObligation(ArgMap, Site.Guard.get(), Site.Loc, &Site.Quantifiers,
                  Callee);
  }

  if (UnsupportedSpecRecursion || UnsupportedExecRecursion) {
    auto PS = std::make_unique<PassiveStmt>();
    PS->K = PassiveStmt::Assert;
    PS->ProofKind = ProofObligationKind::Unsupported;
    PS->Cond = std::make_unique<VLiteralExpr>(false, VType::makeBool(),
                                              Fn.Decreases.front()->Loc);
    P.Stmts.push_back(std::move(PS));
  }
  if (Fn.IsSpec)
    addSpecPostChecks(P, Fn, FnMap);
  return P;
}
namespace {

std::unique_ptr<VExpr> asMathInteger(std::unique_ptr<VExpr> E) {
  if (!E || !E->Ty.isInt() || E->Ty.IntMode == VIntMode::Math)
    return E;
  VType MathTy = E->Ty;
  MathTy.IntMode = VIntMode::Math;
  const VType From = E->Ty;
  const SourceLocation Loc = E->Loc;
  return std::make_unique<VCastExpr>(std::move(E), From, MathTy, Loc);
}

/// [Base, End) in target bytes for one reads range at \p Args.
std::pair<std::unique_ptr<VExpr>, std::unique_ptr<VExpr>>
readRangeBytes(const VReadRange &Range,
               const std::map<std::string, std::unique_ptr<VExpr>> &Args,
               SourceLocation Loc) {
  auto Base = substParamsInExpr(Range.Base.get(), Args);
  auto Count = asMathInteger(substParamsInExpr(Range.Count.get(), Args));
  if (!Base || !Count)
    return {nullptr, nullptr};
  const VType MathTy = Count->Ty;
  std::unique_ptr<VExpr> Bytes = std::move(Count);
  if (Range.ElementSize != 1)
    Bytes = std::make_unique<VBinOpExpr>(
        VBinOp::Mul, std::move(Bytes),
        std::make_unique<VLiteralExpr>(std::to_string(Range.ElementSize),
                                       MathTy, Loc),
        MathTy, Loc);
  auto End = std::make_unique<VBinOpExpr>(VBinOp::Add, cloneVExpr(Base.get()),
                                          std::move(Bytes), Base->Ty, Loc);
  return {std::move(Base), std::move(End)};
}

std::unique_ptr<VExpr> compare(VBinOp Op, std::unique_ptr<VExpr> L,
                               std::unique_ptr<VExpr> R, SourceLocation Loc) {
  return std::make_unique<VBinOpExpr>(Op, std::move(L), std::move(R),
                                      VType::makeBool(), Loc);
}

std::unique_ptr<VExpr> anyOf(std::vector<std::unique_ptr<VExpr>> Terms,
                             SourceLocation Loc) {
  std::unique_ptr<VExpr> Result =
      std::make_unique<VLiteralExpr>(false, VType::makeBool(), Loc);
  for (auto &Term : Terms)
    Result = std::make_unique<VBinOpExpr>(
        VBinOp::Or, std::move(Result), std::move(Term), VType::makeBool(), Loc);
  return Result;
}

/// A load or a spec call in a spec body, with the condition that reaches it.
struct BodySite {
  /// The address of a load.
  std::unique_ptr<VExpr> Address;
  const VSpecCallExpr *Call = nullptr;
  /// The callee of a spec call, if known.
  const VFunction *Callee = nullptr;
  std::vector<std::unique_ptr<VExpr>> Args;
  std::unique_ptr<VExpr> Guard;
  SourceLocation Loc;
  /// Outermost first.
  std::vector<EnclosingQuantifier> Quantifiers;
};

/// A value a spec body returns, with the condition that reaches it.
struct BodyReturn {
  std::unique_ptr<VExpr> Guard;
  std::unique_ptr<VExpr> Value;
  SourceLocation Loc;
};

struct SpecBodyCollector {
  const FunctionMap &FnMap;
  std::vector<BodySite> Sites;
  std::vector<BodyReturn> Returns;
  bool Unsupported = false;

  void site(BodySite Site,
            const std::map<std::string, std::unique_ptr<VExpr>> &Env,
            const VExpr *Guard,
            const std::vector<const VQuantifiedExpr *> &Quantifiers) {
    Site.Guard = cloneVExpr(Guard);
    for (const VQuantifiedExpr *Q : Quantifiers)
      Site.Quantifiers.push_back({Q->Binder, Q->BinderType,
                                  substParamsInExpr(Q->Lo.get(), Env),
                                  substParamsInExpr(Q->Hi.get(), Env)});
    Sites.push_back(std::move(Site));
  }

  void expr(const VExpr *E,
            const std::map<std::string, std::unique_ptr<VExpr>> &Env,
            const VExpr *Guard,
            const std::vector<const VQuantifiedExpr *> &Quantifiers) {
    if (!E)
      return;
    switch (E->K) {
    case VExpr::SpecCall: {
      const auto *C = static_cast<const VSpecCallExpr *>(E);
      BodySite Site;
      Site.Call = C;
      if (auto It = FnMap.find(C->CalleeIdentity); It != FnMap.end())
        Site.Callee = It->second;
      for (const auto &Arg : C->Args)
        Site.Args.push_back(substParamsInExpr(Arg.get(), Env));
      Site.Loc = C->Loc;
      site(std::move(Site), Env, Guard, Quantifiers);
      for (const auto &A : C->Args)
        expr(A.get(), Env, Guard, Quantifiers);
      return;
    }
    case VExpr::Load: {
      const auto *L = static_cast<const VLoadExpr *>(E);
      BodySite Site;
      Site.Address = substParamsInExpr(L->Ptr.get(), Env);
      Site.Loc = L->Loc;
      site(std::move(Site), Env, Guard, Quantifiers);
      expr(L->Ptr.get(), Env, Guard, Quantifiers);
      expr(L->AccessCondition.get(), Env, Guard, Quantifiers);
      return;
    }
    case VExpr::BinOp: {
      const auto *B = static_cast<const VBinOpExpr *>(E);
      expr(B->Lhs.get(), Env, Guard, Quantifiers);
      std::unique_ptr<VExpr> RightGuard = cloneVExpr(Guard);
      if (B->Op == VBinOp::And)
        RightGuard =
            makeDecreaseAnd(std::move(RightGuard),
                            substParamsInExpr(B->Lhs.get(), Env), B->Loc);
      else if (B->Op == VBinOp::Or)
        RightGuard = makeDecreaseAnd(
            std::move(RightGuard),
            makeDecreaseNot(substParamsInExpr(B->Lhs.get(), Env), B->Loc),
            B->Loc);
      expr(B->Rhs.get(), Env, RightGuard.get(), Quantifiers);
      return;
    }
    case VExpr::UnaryOp:
      expr(static_cast<const VUnaryOpExpr *>(E)->Operand.get(), Env, Guard,
           Quantifiers);
      return;
    case VExpr::Cast:
      expr(static_cast<const VCastExpr *>(E)->Inner.get(), Env, Guard,
           Quantifiers);
      return;
    case VExpr::Old:
      expr(static_cast<const VOldExpr *>(E)->Inner.get(), Env, Guard,
           Quantifiers);
      return;
    case VExpr::Conditional: {
      const auto *C = static_cast<const VConditionalExpr *>(E);
      expr(C->Cond.get(), Env, Guard, Quantifiers);
      auto Cond = substParamsInExpr(C->Cond.get(), Env);
      auto ThenGuard =
          makeDecreaseAnd(cloneVExpr(Guard), cloneVExpr(Cond.get()), C->Loc);
      auto ElseGuard = makeDecreaseAnd(
          cloneVExpr(Guard), makeDecreaseNot(std::move(Cond), C->Loc), C->Loc);
      expr(C->Then.get(), Env, ThenGuard.get(), Quantifiers);
      expr(C->Else.get(), Env, ElseGuard.get(), Quantifiers);
      return;
    }
    case VExpr::OverflowCheck: {
      const auto *O = static_cast<const VOverflowCheckExpr *>(E);
      expr(O->Lhs.get(), Env, Guard, Quantifiers);
      expr(O->Rhs.get(), Env, Guard, Quantifiers);
      return;
    }
    case VExpr::Forall:
    case VExpr::Exists: {
      const auto *Q = static_cast<const VQuantifiedExpr *>(E);
      expr(Q->Lo.get(), Env, Guard, Quantifiers);
      expr(Q->Hi.get(), Env, Guard, Quantifiers);
      std::vector<const VQuantifiedExpr *> Inner = Quantifiers;
      Inner.push_back(Q);
      expr(Q->Body.get(), Env, Guard, Inner);
      return;
    }
    case VExpr::FieldAccess:
      expr(static_cast<const VFieldAccessExpr *>(E)->Base.get(), Env, Guard,
           Quantifiers);
      return;
    case VExpr::HeapStore:
    case VExpr::HeapFrame:
      Unsupported = true;
      return;
    case VExpr::Literal:
    case VExpr::Var:
    case VExpr::Result:
      return;
    }
  }

  std::vector<DecreaseState>
  body(const std::vector<std::unique_ptr<VStmt>> &Stmts,
       std::vector<DecreaseState> States) {
    for (const auto &S : Stmts) {
      std::vector<DecreaseState> NextStates;
      for (DecreaseState &State : States) {
        switch (S->K) {
        case VStmt::Assign: {
          const auto &A = static_cast<const VAssignStmt &>(*S);
          expr(A.Value.get(), State.Env, State.Guard.get(), {});
          State.Env[A.Target] = substParamsInExpr(A.Value.get(), State.Env);
          NextStates.push_back(std::move(State));
          break;
        }
        case VStmt::Return: {
          const auto &R = static_cast<const VReturnStmt &>(*S);
          expr(R.Value.get(), State.Env, State.Guard.get(), {});
          Returns.push_back({cloneVExpr(State.Guard.get()),
                             substParamsInExpr(R.Value.get(), State.Env),
                             R.Loc});
          break;
        }
        case VStmt::If: {
          const auto &I = static_cast<const VIfStmt &>(*S);
          expr(I.Cond.get(), State.Env, State.Guard.get(), {});
          auto Cond = substParamsInExpr(I.Cond.get(), State.Env);
          std::vector<DecreaseState> ThenStates;
          ThenStates.push_back(
              {cloneExprMap(State.Env),
               makeDecreaseAnd(cloneVExpr(State.Guard.get()),
                               cloneVExpr(Cond.get()), I.Loc)});
          ThenStates = body(I.Then, std::move(ThenStates));
          std::vector<DecreaseState> ElseStates;
          ElseStates.push_back(
              {std::move(State.Env),
               makeDecreaseAnd(std::move(State.Guard),
                               makeDecreaseNot(std::move(Cond), I.Loc),
                               I.Loc)});
          ElseStates = body(I.Else, std::move(ElseStates));
          for (auto *Part : {&ThenStates, &ElseStates})
            NextStates.insert(NextStates.end(),
                              std::make_move_iterator(Part->begin()),
                              std::make_move_iterator(Part->end()));
          break;
        }
        default:
          Unsupported = true;
          break;
        }
      }
      States = std::move(NextStates);
      if (States.empty())
        break;
    }
    return States;
  }

  void run(const VFunction &Fn) {
    DecreaseState Initial;
    for (const auto &Param : Fn.Params)
      Initial.Env[Param.first] = std::make_unique<VVarExpr>(
          Param.first, Param.second, SourceLocation());
    Initial.Guard =
        std::make_unique<VLiteralExpr>(1, VType::makeBool(), SourceLocation());
    std::vector<DecreaseState> States;
    States.push_back(std::move(Initial));
    // A path that falls off the end returns nothing to check.
    if (!body(Fn.Body, std::move(States)).empty())
      Unsupported = true;
  }
};

} // namespace

std::unique_ptr<VExpr>
verify::addressOutsideReads(const VFunction &Spec,
                            const std::vector<std::unique_ptr<VExpr>> &Args,
                            const VExpr *Address, SourceLocation Loc) {
  auto Map = bindParams(Spec, Args);
  std::unique_ptr<VExpr> Outside =
      std::make_unique<VLiteralExpr>(true, VType::makeBool(), Loc);
  for (const VReadRange &Range : Spec.Reads) {
    auto [Base, End] = readRangeBytes(Range, Map, Loc);
    if (!Base)
      return nullptr;
    auto Disjoint = std::make_unique<VBinOpExpr>(
        VBinOp::Or,
        compare(VBinOp::Lt, cloneVExpr(Address), std::move(Base), Loc),
        compare(VBinOp::Ge, cloneVExpr(Address), std::move(End), Loc),
        VType::makeBool(), Loc);
    Outside = makeDecreaseAnd(std::move(Outside), std::move(Disjoint), Loc);
  }
  return Outside;
}

std::unique_ptr<VExpr>
verify::regionOutsideReads(const VFunction &Spec,
                           const std::vector<std::unique_ptr<VExpr>> &Args,
                           const VExpr *Lo, const VExpr *Hi,
                           SourceLocation Loc) {
  auto Map = bindParams(Spec, Args);
  std::unique_ptr<VExpr> Outside =
      std::make_unique<VLiteralExpr>(true, VType::makeBool(), Loc);
  for (const VReadRange &Range : Spec.Reads) {
    auto [Base, End] = readRangeBytes(Range, Map, Loc);
    if (!Base)
      return nullptr;
    auto Disjoint = std::make_unique<VBinOpExpr>(
        VBinOp::Or, compare(VBinOp::Le, cloneVExpr(Hi), std::move(Base), Loc),
        compare(VBinOp::Le, std::move(End), cloneVExpr(Lo), Loc),
        VType::makeBool(), Loc);
    Outside = makeDecreaseAnd(std::move(Outside), std::move(Disjoint), Loc);
  }
  return Outside;
}

PassiveProgram verify::buildReadsChecks(const VFunction &Fn,
                                        const FunctionMap &FnMap,
                                        std::string &Missing) {
  PassiveProgram P;
  P.FunctionName = Fn.Name + ".reads";
  P.FunctionIdentity = Fn.Identity + "::reads";
  P.CallerIntMode = Fn.IntMode;
  P.SpecFunctions = FnMap;
  P.SpecFuel = Fn.SpecFuel;
  P.HiddenSpecs = Fn.HiddenSpecs;
  P.HiddenSpecs.insert(Fn.Identity);
  P.HiddenSpecs.insert(Fn.RecursionGroup.begin(), Fn.RecursionGroup.end());
  P.RevealedSpecs = Fn.RevealedSpecs;

  SpecBodyCollector Collector{FnMap};
  Collector.run(Fn);
  std::map<std::string, std::unique_ptr<VExpr>> Self;
  for (const auto &Param : Fn.Params)
    Self[Param.first] =
        std::make_unique<VVarExpr>(Param.first, Param.second, SourceLocation());

  auto contained = [&](const VExpr *Start, const VExpr *Stop,
                       SourceLocation Loc) {
    std::vector<std::unique_ptr<VExpr>> Within;
    for (const VReadRange &Range : Fn.Reads) {
      auto [Base, End] = readRangeBytes(Range, Self, Loc);
      if (!Base)
        continue;
      auto Lower = compare(VBinOp::Ge, cloneVExpr(Start), std::move(Base), Loc);
      auto Upper =
          Stop ? compare(VBinOp::Le, cloneVExpr(Stop), std::move(End), Loc)
               : compare(VBinOp::Lt, cloneVExpr(Start), std::move(End), Loc);
      Within.push_back(
          makeDecreaseAnd(std::move(Lower), std::move(Upper), Loc));
    }
    return anyOf(std::move(Within), Loc);
  };

  for (BodySite &Site : Collector.Sites) {
    if (!Site.Address && !Site.Call->ReadsHeap)
      continue;
    if (!Site.Address && (!Site.Callee || Site.Callee->Reads.empty())) {
      if (Missing.empty())
        Missing = Site.Call->Callee;
      continue;
    }
    std::unique_ptr<VExpr> Obligation;
    if (Site.Address) {
      Obligation = contained(Site.Address.get(), nullptr, Site.Loc);
    } else {
      // Each callee range is empty or inside one of ours.
      Obligation =
          std::make_unique<VLiteralExpr>(true, VType::makeBool(), Site.Loc);
      auto CalleeArgs = bindParams(*Site.Callee, Site.Args);
      for (const VReadRange &Range : Site.Callee->Reads) {
        auto [Base, End] = readRangeBytes(Range, CalleeArgs, Site.Loc);
        if (!Base)
          continue;
        auto Empty = compare(VBinOp::Le, cloneVExpr(End.get()),
                             cloneVExpr(Base.get()), Site.Loc);
        auto Inside = contained(Base.get(), End.get(), Site.Loc);
        Obligation =
            makeDecreaseAnd(std::move(Obligation),
                            std::make_unique<VBinOpExpr>(
                                VBinOp::Or, std::move(Empty), std::move(Inside),
                                VType::makeBool(), Site.Loc),
                            Site.Loc);
      }
    }
    if (Site.Guard)
      Obligation = std::make_unique<VBinOpExpr>(
          VBinOp::Or, makeDecreaseNot(cloneVExpr(Site.Guard.get()), Site.Loc),
          std::move(Obligation), VType::makeBool(), Site.Loc);
    for (auto It = Site.Quantifiers.rbegin(); It != Site.Quantifiers.rend();
         ++It)
      Obligation = std::make_unique<VForallExpr>(
          It->Binder, cloneVExpr(It->Lo.get()), cloneVExpr(It->Hi.get()),
          std::move(Obligation), Site.Loc, It->BinderType);
    auto PS = std::make_unique<PassiveStmt>();
    PS->K = PassiveStmt::Assert;
    PS->ProofKind = ProofObligationKind::Frame;
    PS->Cond = cloneAtEntryState(Obligation.get());
    P.Stmts.push_back(std::move(PS));
  }
  if (Collector.Unsupported) {
    auto PS = std::make_unique<PassiveStmt>();
    PS->K = PassiveStmt::Assert;
    PS->ProofKind = ProofObligationKind::Unsupported;
    PS->Cond = std::make_unique<VLiteralExpr>(false, VType::makeBool(),
                                              SourceLocation());
    P.Stmts.push_back(std::move(PS));
  }
  return P;
}

/// Points the heap reads of a spec's own clause at \p Heap.
static void readHeapAt(VExpr *E, const std::string &Heap) {
  if (!E)
    return;
  switch (E->K) {
  case VExpr::Load: {
    auto *L = static_cast<VLoadExpr *>(E);
    if (L->HeapVar.empty() || L->HeapVar == VSpecHeapName)
      L->HeapVar = Heap;
    readHeapAt(L->Ptr.get(), Heap);
    readHeapAt(L->AccessCondition.get(), Heap);
    return;
  }
  case VExpr::SpecCall: {
    auto *C = static_cast<VSpecCallExpr *>(E);
    if (C->ReadsHeap && (C->HeapVar.empty() || C->HeapVar == VSpecHeapName))
      C->HeapVar = Heap;
    for (auto &Arg : C->Args)
      readHeapAt(Arg.get(), Heap);
    return;
  }
  case VExpr::BinOp: {
    auto *B = static_cast<VBinOpExpr *>(E);
    readHeapAt(B->Lhs.get(), Heap);
    readHeapAt(B->Rhs.get(), Heap);
    return;
  }
  case VExpr::UnaryOp:
    readHeapAt(static_cast<VUnaryOpExpr *>(E)->Operand.get(), Heap);
    return;
  case VExpr::Cast:
    readHeapAt(static_cast<VCastExpr *>(E)->Inner.get(), Heap);
    return;
  case VExpr::Old:
    readHeapAt(static_cast<VOldExpr *>(E)->Inner.get(), Heap);
    return;
  case VExpr::Conditional: {
    auto *C = static_cast<VConditionalExpr *>(E);
    readHeapAt(C->Cond.get(), Heap);
    readHeapAt(C->Then.get(), Heap);
    readHeapAt(C->Else.get(), Heap);
    return;
  }
  case VExpr::Forall:
  case VExpr::Exists: {
    auto *Q = static_cast<VQuantifiedExpr *>(E);
    readHeapAt(Q->Lo.get(), Heap);
    readHeapAt(Q->Hi.get(), Heap);
    readHeapAt(Q->Body.get(), Heap);
    return;
  }
  case VExpr::FieldAccess:
    readHeapAt(static_cast<VFieldAccessExpr *>(E)->Base.get(), Heap);
    return;
  case VExpr::OverflowCheck: {
    auto *O = static_cast<VOverflowCheckExpr *>(E);
    readHeapAt(O->Lhs.get(), Heap);
    readHeapAt(O->Rhs.get(), Heap);
    return;
  }
  case VExpr::HeapStore:
  case VExpr::HeapFrame:
  case VExpr::Literal:
  case VExpr::Var:
  case VExpr::Result:
    return;
  }
}

std::unique_ptr<VExpr> verify::specPostcondition(
    const VFunction &Spec, const std::vector<std::unique_ptr<VExpr>> &Args,
    const VExpr *Value, SourceLocation Loc, const std::string &Heap) {
  if (Spec.Postconditions.empty())
    return nullptr;
  auto Map = bindParams(Spec, Args);
  Map[ResultKey] = cloneVExpr(Value);
  std::unique_ptr<VExpr> Holds =
      std::make_unique<VLiteralExpr>(true, VType::makeBool(), Loc);
  for (const auto &Post : Spec.Postconditions) {
    auto Clause = cloneVExpr(Post.get());
    if (!Heap.empty())
      readHeapAt(Clause.get(), Heap);
    Holds = makeDecreaseAnd(std::move(Holds),
                            substParamsInExpr(Clause.get(), Map), Loc);
  }
  return Holds;
}

/// The postconditions of the specs a spec body calls, and of the spec itself
/// at each return. A call within the recursion cycle may assume its callee's
/// postcondition only where the measure is lower: the postconditions and
/// termination are proved together by well-founded induction on the measure.
static void addSpecPostChecks(PassiveProgram &P, const VFunction &Fn,
                              const FunctionMap &FnMap) {
  SpecBodyCollector Collector{FnMap};
  Collector.run(Fn);
  std::map<std::string, std::unique_ptr<VExpr>> Self;
  for (const auto &Param : Fn.Params)
    Self[Param.first] =
        std::make_unique<VVarExpr>(Param.first, Param.second, SourceLocation());
  std::vector<std::unique_ptr<VExpr>> CurrentDec;
  for (const auto &Decrease : Fn.Decreases)
    CurrentDec.push_back(substParamsInExpr(Decrease.get(), Self));

  std::vector<std::unique_ptr<PassiveStmt>> Facts;
  for (BodySite &Site : Collector.Sites) {
    if (!Site.Call || !Site.Callee || Site.Callee->Postconditions.empty())
      continue;
    const VSpecCallExpr &Call = *Site.Call;
    std::vector<std::unique_ptr<VExpr>> Args;
    for (const auto &Arg : Site.Args)
      Args.push_back(cloneVExpr(Arg.get()));
    auto Application = std::make_unique<VSpecCallExpr>(
        Call.Callee, Call.CalleeIdentity, std::move(Args), Call.Ty, Call.Loc,
        Call.ReadsHeap, Call.HeapVar);
    std::unique_ptr<VExpr> Fact =
        specPostcondition(*Site.Callee, Site.Args, Application.get(), Site.Loc);
    if (!Fact)
      continue;
    const bool InCycle = Call.CalleeIdentity == Fn.Identity ||
                         Fn.RecursionGroup.count(Call.CalleeIdentity);
    if (InCycle) {
      auto ArgMap = bindParams(*Site.Callee, Site.Args);
      std::vector<std::unique_ptr<VExpr>> CalleeDec;
      bool Complete = Site.Callee->Decreases.size() == CurrentDec.size() &&
                      !CurrentDec.empty();
      for (const auto &Decrease : Site.Callee->Decreases) {
        CalleeDec.push_back(substParamsInExpr(Decrease.get(), ArgMap));
        Complete = Complete && CalleeDec.back();
      }
      if (!Complete)
        continue;
      Fact = std::make_unique<VBinOpExpr>(
          VBinOp::Or,
          makeDecreaseNot(
              lexicographicDecrease(CalleeDec, CurrentDec, Site.Loc), Site.Loc),
          std::move(Fact), VType::makeBool(), Site.Loc);
    }
    for (auto It = Site.Quantifiers.rbegin(); It != Site.Quantifiers.rend();
         ++It)
      Fact = std::make_unique<VForallExpr>(
          It->Binder, cloneVExpr(It->Lo.get()), cloneVExpr(It->Hi.get()),
          std::move(Fact), Site.Loc, It->BinderType);
    auto PS = std::make_unique<PassiveStmt>();
    PS->K = PassiveStmt::Assume;
    PS->Cond = cloneAtEntryState(Fact.get());
    Facts.push_back(std::move(PS));
  }
  P.Stmts.insert(P.Stmts.begin(), std::make_move_iterator(Facts.begin()),
                 std::make_move_iterator(Facts.end()));

  if (Fn.Postconditions.empty())
    return;
  std::vector<std::unique_ptr<VExpr>> Params;
  for (const auto &Param : Fn.Params)
    Params.push_back(std::make_unique<VVarExpr>(Param.first, Param.second,
                                                SourceLocation()));
  for (BodyReturn &Return : Collector.Returns) {
    std::unique_ptr<VExpr> Obligation =
        specPostcondition(Fn, Params, Return.Value.get(), Return.Loc);
    Obligation = std::make_unique<VBinOpExpr>(
        VBinOp::Or, makeDecreaseNot(std::move(Return.Guard), Return.Loc),
        std::move(Obligation), VType::makeBool(), Return.Loc);
    Obligation->Loc = Fn.Postconditions.front()->Loc;
    auto PS = std::make_unique<PassiveStmt>();
    PS->K = PassiveStmt::Assert;
    PS->ProofKind = ProofObligationKind::Postcondition;
    PS->Cond = cloneAtEntryState(Obligation.get());
    P.Stmts.push_back(std::move(PS));
  }
  if (Collector.Unsupported) {
    auto PS = std::make_unique<PassiveStmt>();
    PS->K = PassiveStmt::Assert;
    PS->ProofKind = ProofObligationKind::Unsupported;
    PS->Cond = std::make_unique<VLiteralExpr>(false, VType::makeBool(),
                                              Fn.Postconditions.front()->Loc);
    P.Stmts.push_back(std::move(PS));
  }
}

PassiveProgram verify::buildSpecPostChecks(const VFunction &Fn,
                                           const FunctionMap &FnMap) {
  PassiveProgram P;
  P.FunctionName = Fn.Name + ".post";
  P.FunctionIdentity = Fn.Identity + "::post";
  P.CallerIntMode = Fn.IntMode;
  P.SpecFunctions = FnMap;
  P.SpecFuel = Fn.SpecFuel;
  P.HiddenSpecs = Fn.HiddenSpecs;
  P.HiddenSpecs.insert(Fn.Identity);
  P.RevealedSpecs = Fn.RevealedSpecs;
  addSpecPostChecks(P, Fn, FnMap);
  return P;
}
