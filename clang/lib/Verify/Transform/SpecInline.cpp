//===--- SpecInline.cpp ---------------------------------------------------===//
#include "SpecInline.h"
#include "../Transform/Passivize.h"
#include <map>
#include <set>
#include <vector>

using namespace clang;
using namespace verify;

static std::map<std::string, std::unique_ptr<VExpr>>
bindParams(const VFunction &Fn,
           const std::vector<std::unique_ptr<VExpr>> &Args) {
  std::map<std::string, std::unique_ptr<VExpr>> Env;
  for (unsigned I = 0; I < Fn.Params.size() && I < Args.size(); ++I)
    Env[Fn.Params[I].first] = cloneVExpr(Args[I].get());
  return Env;
}

static std::unique_ptr<VExpr> envLookup(const std::map<std::string, std::unique_ptr<VExpr>> &Env,
                                        const std::string &Name, VType Ty,
                                        SourceLocation Loc) {
  if (auto It = Env.find(Name); It != Env.end())
    return cloneVExpr(It->second.get());
  return std::make_unique<VVarExpr>(Name, Ty, Loc);
}

class SpecInlinerImpl {
  const FunctionMap &FnMap;
  std::map<std::string, unsigned> Fuel;
  std::set<std::string> Hidden;
  std::set<std::string> Revealed;
  unsigned OpaqueId = 0;
  unsigned InlineDepth = 0;
  static constexpr unsigned MaxInlineDepth = 256;

  unsigned fuelFor(const std::string &Name) const {
    if (Hidden.count(Name))
      return 0;
    if (auto It = Fuel.find(Name); It != Fuel.end())
      return It->second;
    auto It = FnMap.find(Name);
    if (It != FnMap.end() && It->second->NeedsDecreasesCheck)
      return 0;
    return 1;
  }

  std::unique_ptr<VExpr> opaqueCall(const VSpecCallExpr &C) {
    std::string Name = "__spec_" + C.Callee + "_" + std::to_string(++OpaqueId);
    return std::make_unique<VVarExpr>(Name, C.Ty, C.Loc);
  }

public:
  SpecInlinerImpl(const FunctionMap &FnMap, std::map<std::string, unsigned> Fuel,
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
    if (Hidden.count(C.Callee))
      return opaqueCall(C);
    auto It = FnMap.find(C.Callee);
    if (It == FnMap.end() || !It->second->IsSpec)
      return opaqueCall(C);
    const VFunction &Spec = *It->second;
    unsigned F = fuelFor(C.Callee);
    if (Revealed.count(C.Callee) && F == 0)
      F = 1;
    if (Spec.NeedsDecreasesCheck) {
      if (F == 0)
        return opaqueCall(C);
      auto Env = bindParams(Spec, C.Args);
      auto OldFuel = Fuel[Spec.Name];
      Fuel[Spec.Name] = F > 0 ? F - 1 : 0;
      auto Out = evalBody(Spec.Body, Env);
      Fuel[Spec.Name] = OldFuel;
      if (!Out)
        return opaqueCall(C);
      return Out;
    }
    auto Env = bindParams(Spec, C.Args);
    if (auto Out = evalBody(Spec.Body, Env))
      return Out;
    return opaqueCall(C);
  }

  std::unique_ptr<VExpr> evalExpr(const VExpr *E,
                                  const std::map<std::string, std::unique_ptr<VExpr>> &Env) {
    if (!E)
      return nullptr;
    switch (E->K) {
    case VExpr::Literal:
      return cloneVExpr(E);
    case VExpr::Var:
      return envLookup(Env, static_cast<const VVarExpr *>(E)->Name, E->Ty, E->Loc);
    case VExpr::BinOp: {
      const auto *B = static_cast<const VBinOpExpr *>(E);
      auto L = evalExpr(B->Lhs.get(), Env);
      auto R = evalExpr(B->Rhs.get(), Env);
      if (!L || !R)
        return nullptr;
      return std::make_unique<VBinOpExpr>(B->Op, std::move(L), std::move(R), B->Ty, B->Loc);
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
      return std::make_unique<VCastExpr>(std::move(I), C->FromTy, C->Ty, C->Loc);
    }
    case VExpr::Conditional: {
      const auto *C = static_cast<const VConditionalExpr *>(E);
      auto Cond = evalExpr(C->Cond.get(), Env);
      auto T = evalExpr(C->Then.get(), Env);
      auto F = evalExpr(C->Else.get(), Env);
      if (!Cond || !T || !F)
        return nullptr;
      return std::make_unique<VConditionalExpr>(std::move(Cond), std::move(T), std::move(F),
                                               C->Ty, C->Loc);
    }
    case VExpr::SpecCall:
      return inlineSpecCall(*static_cast<const VSpecCallExpr *>(E));
    case VExpr::Forall:
    case VExpr::Exists: {
      const auto *Q = static_cast<const VQuantifiedExpr *>(E);
      auto Body = evalExpr(Q->Body.get(), Env);
      if (!Body)
        return nullptr;
      if (E->K == VExpr::Forall)
        return std::unique_ptr<VExpr>(std::make_unique<VForallExpr>(
            Q->Binder, cloneVExpr(Q->Lo.get()), cloneVExpr(Q->Hi.get()),
            std::move(Body), Q->Loc));
      return std::unique_ptr<VExpr>(std::make_unique<VExistsExpr>(
          Q->Binder, cloneVExpr(Q->Lo.get()), cloneVExpr(Q->Hi.get()),
          std::move(Body), Q->Loc));
    }
    default:
      return cloneVExpr(E);
    }
  }

  std::unique_ptr<VExpr> evalBodySeq(
      const std::vector<std::unique_ptr<VStmt>> &Body,
      std::map<std::string, std::unique_ptr<VExpr>> &Env, unsigned Idx) {
    if (Idx >= Body.size())
      return nullptr;
    const VStmt &S = *Body[Idx];
    switch (S.K) {
    case VStmt::Assign: {
      const auto &A = static_cast<const VAssignStmt &>(S);
      Env[A.Target] = evalExpr(A.Value.get(), Env);
      return evalBodySeq(Body, Env, Idx + 1);
    }
    case VStmt::Return: {
      const auto &R = static_cast<const VReturnStmt &>(S);
      return evalExpr(R.Value.get(), Env);
    }
    case VStmt::If: {
      const auto &I = static_cast<const VIfStmt &>(S);
      auto Cond = evalExpr(I.Cond.get(), Env);
      if (!Cond)
        return nullptr;
      if (I.Else.empty()) {
        auto ThenEnv = cloneEnv(Env);
        auto ThenVal = evalBody(I.Then, ThenEnv);
        auto Rest = evalBodySeq(Body, Env, Idx + 1);
        if (!ThenVal || !Rest)
          return nullptr;
        return std::make_unique<VConditionalExpr>(std::move(Cond), std::move(ThenVal),
                                                  std::move(Rest), ThenVal->Ty, I.Loc);
      }
      auto ThenEnv = cloneEnv(Env);
      auto ElseEnv = cloneEnv(Env);
      auto ThenVal = evalBody(I.Then, ThenEnv);
      auto ElseVal = evalBody(I.Else, ElseEnv);
      if (!ThenVal || !ElseVal)
        return nullptr;
      return std::make_unique<VConditionalExpr>(std::move(Cond), std::move(ThenVal),
                                                std::move(ElseVal), ThenVal->Ty, I.Loc);
    }
    case VStmt::GhostBlock: {
      const auto &G = static_cast<const VGhostBlockStmt &>(S);
      if (auto R = evalBody(G.Body, Env))
        return R;
      return evalBodySeq(Body, Env, Idx + 1);
    }
    default:
      return evalBodySeq(Body, Env, Idx + 1);
    }
  }

  static std::map<std::string, std::unique_ptr<VExpr>>
  cloneEnv(const std::map<std::string, std::unique_ptr<VExpr>> &Env) {
    std::map<std::string, std::unique_ptr<VExpr>> Out;
    for (const auto &[K, V] : Env)
      Out[K] = cloneVExpr(V.get());
    return Out;
  }

  std::unique_ptr<VExpr> evalBody(const std::vector<std::unique_ptr<VStmt>> &Body,
                                  std::map<std::string, std::unique_ptr<VExpr>> &Env) {
    return evalBodySeq(Body, Env, 0);
  }

  void inlineStmts(std::vector<std::unique_ptr<VStmt>> &Stmts) {
    for (auto &S : Stmts) {
      switch (S->K) {
      case VStmt::Assign: {
        auto &A = static_cast<VAssignStmt &>(*S);
        A.Value = inlineExpr(std::move(A.Value));
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
        if (W.Decreases)
          W.Decreases = inlineExpr(std::move(W.Decreases));
        inlineStmts(W.Body);
        break;
      }
      case VStmt::ContractAssert: {
        auto &A = static_cast<VContractAssertStmt &>(*S);
        A.Cond = inlineExpr(std::move(A.Cond));
        break;
      }
      case VStmt::GhostBlock: {
        auto &G = static_cast<VGhostBlockStmt &>(*S);
        inlineStmts(G.Body);
        break;
      }
      default:
        break;
      }
    }
  }
};

static std::unique_ptr<VExpr> opaqueSpecExpr(const VExpr *E, unsigned &Id) {
  if (!E)
    return nullptr;
  if (E->K == VExpr::SpecCall) {
    const auto *C = static_cast<const VSpecCallExpr *>(E);
    return std::make_unique<VVarExpr>("__spec_" + C->Callee + "_" + std::to_string(++Id),
                                     C->Ty, C->Loc);
  }
  if (E->K == VExpr::BinOp) {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    return std::make_unique<VBinOpExpr>(
        B->Op, opaqueSpecExpr(B->Lhs.get(), Id), opaqueSpecExpr(B->Rhs.get(), Id), B->Ty,
        B->Loc);
  }
  if (E->K == VExpr::UnaryOp) {
    const auto *U = static_cast<const VUnaryOpExpr *>(E);
    return std::make_unique<VUnaryOpExpr>(
        U->Op, opaqueSpecExpr(U->Operand.get(), Id), U->Ty, U->Loc);
  }
  if (E->K == VExpr::Old)
    return opaqueSpecExpr(static_cast<const VOldExpr *>(E)->Inner.get(), Id);
  if (E->K == VExpr::Conditional) {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    return std::make_unique<VConditionalExpr>(
        opaqueSpecExpr(C->Cond.get(), Id), opaqueSpecExpr(C->Then.get(), Id),
        opaqueSpecExpr(C->Else.get(), Id), C->Ty, C->Loc);
  }
  return cloneVExpr(E);
}

static void opaqueAllSpecCalls(VFunction &Fn) {
  unsigned Id = 0;
  for (auto &P : Fn.Preconditions)
    P = opaqueSpecExpr(P.get(), Id);
  for (auto &P : Fn.Postconditions)
    P = opaqueSpecExpr(P.get(), Id);
  for (auto &R : Fn.Recommends)
    R = opaqueSpecExpr(R.get(), Id);
}

void SpecInliner::prepareFunctionAxiomatic(VFunction &Fn) {
  (void)Fn;
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
  Impl.inlineStmts(Fn.Body);
}

std::unique_ptr<VExpr> SpecInliner::unfoldDefinition(
    const VFunction &Spec, const std::map<std::string, unsigned> &FuelMap,
    const std::set<std::string> &Hidden, const std::set<std::string> &Revealed,
    unsigned RootFuel) const {
  std::vector<std::unique_ptr<VExpr>> Args;
  for (const auto &P : Spec.Params)
    Args.push_back(
        std::make_unique<VVarExpr>(P.first, P.second, SourceLocation()));
  auto Call = std::make_unique<VSpecCallExpr>(Spec.Name, std::move(Args),
                                              Spec.ReturnType, SourceLocation());
  std::map<std::string, unsigned> Fuel = FuelMap;
  Fuel[Spec.Name] = std::max(Fuel[Spec.Name], RootFuel);
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
  if (E->K == VExpr::SpecCall)
    Out.push_back(static_cast<const VSpecCallExpr *>(E));
  if (E->K == VExpr::BinOp) {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    collectSpecCalls(B->Lhs.get(), Out);
    collectSpecCalls(B->Rhs.get(), Out);
  } else if (E->K == VExpr::UnaryOp) {
    collectSpecCalls(static_cast<const VUnaryOpExpr *>(E)->Operand.get(), Out);
  } else if (E->K == VExpr::Conditional) {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    collectSpecCalls(C->Cond.get(), Out);
    collectSpecCalls(C->Then.get(), Out);
    collectSpecCalls(C->Else.get(), Out);
  } else if (E->K == VExpr::Old) {
    collectSpecCalls(static_cast<const VOldExpr *>(E)->Inner.get(), Out);
  }
}

void verify::collectSpecCallsInFunction(const VFunction &Fn,
                                      std::vector<const VSpecCallExpr *> &Out) {
  for (const auto &P : Fn.Preconditions)
    collectSpecCalls(P.get(), Out);
  for (const auto &P : Fn.Postconditions)
    collectSpecCalls(P.get(), Out);
  for (const auto &S : Fn.Body) {
    if (S->K == VStmt::Assign)
      collectSpecCalls(static_cast<const VAssignStmt &>(*S).Value.get(), Out);
    if (S->K == VStmt::Return)
      collectSpecCalls(static_cast<const VReturnStmt &>(*S).Value.get(), Out);
  }
}



std::unique_ptr<VExpr>
verify::substParamsInExpr(const VExpr *E,
                          const std::map<std::string, std::unique_ptr<VExpr>> &Map) {
  if (!E)
    return nullptr;
  if (E->K == VExpr::Var) {
    const auto *V = static_cast<const VVarExpr *>(E);
    if (auto It = Map.find(V->Name); It != Map.end())
      return cloneVExpr(It->second.get());
    return cloneVExpr(E);
  }
  if (E->K == VExpr::BinOp) {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    return std::make_unique<VBinOpExpr>(
        B->Op, substParamsInExpr(B->Lhs.get(), Map), substParamsInExpr(B->Rhs.get(), Map),
        B->Ty, B->Loc);
  }
  if (E->K == VExpr::UnaryOp) {
    const auto *U = static_cast<const VUnaryOpExpr *>(E);
    return std::make_unique<VUnaryOpExpr>(
        U->Op, substParamsInExpr(U->Operand.get(), Map), U->Ty, U->Loc);
  }
  return cloneVExpr(E);
}

static void collectRecursiveCalls(
    const std::vector<std::unique_ptr<VStmt>> &Stmts, const std::string &Self,
    const FunctionMap &FnMap,
    std::vector<std::pair<const VCallStmt *, std::map<std::string, std::unique_ptr<VExpr>>>>
        &Sites,
    std::map<std::string, std::unique_ptr<VExpr>> &Env) {
  for (const auto &S : Stmts) {
    switch (S->K) {
    case VStmt::Assign: {
      const auto &A = static_cast<const VAssignStmt &>(*S);
      Env[A.Target] = cloneVExpr(A.Value.get());
      break;
    }
    case VStmt::Call: {
      const auto &C = static_cast<const VCallStmt &>(*S);
      auto It = FnMap.find(C.Callee);
      if (It != FnMap.end() && It->second->IsSpec &&
          (C.Callee == Self || It->second->NeedsDecreasesCheck)) {
        std::map<std::string, std::unique_ptr<VExpr>> Args;
        for (unsigned I = 0; I < It->second->Params.size() && I < C.Args.size(); ++I)
          Args[It->second->Params[I].first] = cloneVExpr(C.Args[I].get());
        Sites.emplace_back(&C, std::move(Args));
      }
      break;
    }
    case VStmt::If: {
      const auto &I = static_cast<const VIfStmt &>(*S);
      collectRecursiveCalls(I.Then, Self, FnMap, Sites, Env);
      collectRecursiveCalls(I.Else, Self, FnMap, Sites, Env);
      break;
    }
    case VStmt::While: {
      const auto &W = static_cast<const VWhileStmt &>(*S);
      collectRecursiveCalls(W.Body, Self, FnMap, Sites, Env);
      break;
    }
    case VStmt::GhostBlock:
      collectRecursiveCalls(static_cast<const VGhostBlockStmt &>(*S).Body, Self, FnMap,
                            Sites, Env);
      break;
    default:
      break;
    }
  }
}

bool verify::functionHasRecursiveSpecCall(const VFunction &Fn,
                                          const FunctionMap &FnMap) {
  std::vector<std::pair<const VCallStmt *,
                        std::map<std::string, std::unique_ptr<VExpr>>>>
      Sites;
  std::map<std::string, std::unique_ptr<VExpr>> Env;
  collectRecursiveCalls(Fn.Body, Fn.Name, FnMap, Sites, Env);
  if (!Sites.empty())
    return true;
  for (const auto &S : Fn.Body)
    if (S->K == VStmt::Call && static_cast<const VCallStmt &>(*S).Callee == Fn.Name)
      return true;
  return false;
}

static void collectRecursiveSpecCallsInExpr(
    const VExpr *E, const VFunction &Fn,
    std::vector<std::map<std::string, std::unique_ptr<VExpr>>> &ArgMaps) {
  if (!E)
    return;
  if (E->K == VExpr::SpecCall) {
    const auto *C = static_cast<const VSpecCallExpr *>(E);
    if (C->Callee == Fn.Name) {
      std::map<std::string, std::unique_ptr<VExpr>> Args;
      for (unsigned I = 0; I < Fn.Params.size() && I < C->Args.size(); ++I)
        Args[Fn.Params[I].first] = cloneVExpr(C->Args[I].get());
      ArgMaps.push_back(std::move(Args));
    }
    for (const auto &A : C->Args)
      collectRecursiveSpecCallsInExpr(A.get(), Fn, ArgMaps);
    return;
  }
  if (E->K == VExpr::BinOp) {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    collectRecursiveSpecCallsInExpr(B->Lhs.get(), Fn, ArgMaps);
    collectRecursiveSpecCallsInExpr(B->Rhs.get(), Fn, ArgMaps);
  } else if (E->K == VExpr::UnaryOp) {
    collectRecursiveSpecCallsInExpr(
        static_cast<const VUnaryOpExpr *>(E)->Operand.get(), Fn, ArgMaps);
  } else if (E->K == VExpr::Conditional) {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    collectRecursiveSpecCallsInExpr(C->Cond.get(), Fn, ArgMaps);
    collectRecursiveSpecCallsInExpr(C->Then.get(), Fn, ArgMaps);
    collectRecursiveSpecCallsInExpr(C->Else.get(), Fn, ArgMaps);
  }
}

static void collectRecursiveSpecCallsInBody(
    const std::vector<std::unique_ptr<VStmt>> &Stmts, const VFunction &Fn,
    std::vector<std::map<std::string, std::unique_ptr<VExpr>>> &ArgMaps) {
  for (const auto &S : Stmts) {
    if (S->K == VStmt::Return)
      collectRecursiveSpecCallsInExpr(
          static_cast<const VReturnStmt &>(*S).Value.get(), Fn, ArgMaps);
    if (S->K == VStmt::Assign)
      collectRecursiveSpecCallsInExpr(
          static_cast<const VAssignStmt &>(*S).Value.get(), Fn, ArgMaps);
    if (S->K == VStmt::If) {
      const auto &I = static_cast<const VIfStmt &>(*S);
      collectRecursiveSpecCallsInBody(I.Then, Fn, ArgMaps);
      collectRecursiveSpecCallsInBody(I.Else, Fn, ArgMaps);
    }
    if (S->K == VStmt::GhostBlock)
      collectRecursiveSpecCallsInBody(
          static_cast<const VGhostBlockStmt &>(*S).Body, Fn, ArgMaps);
  }
}

PassiveProgram verify::buildDecreasesChecks(const VFunction &Fn,
                                            const FunctionMap &FnMap) {
  PassiveProgram P;
  if (!Fn.Decreases)
    return P;

  std::vector<std::pair<const VCallStmt *,
                        std::map<std::string, std::unique_ptr<VExpr>>>>
      Sites;
  std::map<std::string, std::unique_ptr<VExpr>> Env;
  for (const auto &P : Fn.Params)
    Env[P.first] = std::make_unique<VVarExpr>(P.first, P.second, SourceLocation());
  collectRecursiveCalls(Fn.Body, Fn.Name, FnMap, Sites, Env);

  std::vector<std::map<std::string, std::unique_ptr<VExpr>>> SpecArgMaps;
  collectRecursiveSpecCallsInBody(Fn.Body, Fn, SpecArgMaps);
  for (auto &Args : SpecArgMaps)
    Sites.emplace_back(nullptr, std::move(Args));

  std::map<std::string, std::unique_ptr<VExpr>> EntryEnv;
  for (const auto &P : Fn.Params)
    EntryEnv[P.first] = std::make_unique<VVarExpr>(P.first, P.second, SourceLocation());
  auto CurrentDec = substParamsInExpr(Fn.Decreases.get(), EntryEnv);

  for (const auto &[Call, ArgMap] : Sites) {
    auto CalleeDec = substParamsInExpr(Fn.Decreases.get(), ArgMap);
    if (!CalleeDec || !CurrentDec)
      continue;
    SourceLocation Loc = Call ? Call->Loc : Fn.Decreases->Loc;
    auto PS = std::make_unique<PassiveStmt>();
    PS->K = PassiveStmt::Assert;
    PS->Cond = std::make_unique<VBinOpExpr>(VBinOp::Lt, std::move(CalleeDec),
                                            cloneVExpr(CurrentDec.get()),
                                            VType::makeBool(), Loc);
    P.Stmts.push_back(std::move(PS));
  }
  return P;
}