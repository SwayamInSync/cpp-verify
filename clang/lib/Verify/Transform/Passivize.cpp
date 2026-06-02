//===--- Passivize.cpp ----------------------------------------------------===//
#include "Passivize.h"
#include <map>
#include <set>
#include <string>

using namespace clang;
using namespace verify;

struct CloneCtx {
  const std::map<std::string, std::string> &Renames;
  const std::map<std::string, std::unique_ptr<VExpr>> &OldState;
  bool UseOldState = false;
};

static std::unique_ptr<VExpr> cloneExpr(const VExpr *E, const CloneCtx &Ctx);

static std::unique_ptr<VExpr> cloneExpr(const VExpr *E, const CloneCtx &Ctx) {
  if (!E)
    return nullptr;
  if (Ctx.UseOldState && E->K == VExpr::Old) {
    const auto *O = static_cast<const VOldExpr *>(E);
    CloneCtx Inner{Ctx.Renames, Ctx.OldState, true};
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
    if (Ctx.UseOldState) {
      if (auto It = Ctx.OldState.find(Name); It != Ctx.OldState.end())
        return cloneExpr(It->second.get(), CloneCtx{Ctx.Renames, Ctx.OldState, false});
    }
    if (auto It = Ctx.Renames.find(Name); It != Ctx.Renames.end())
      Name = It->second;
    return std::make_unique<VVarExpr>(Name, V->Ty, V->Loc);
  }
  case VExpr::BinOp: {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    return std::make_unique<VBinOpExpr>(
        B->Op, cloneExpr(B->Lhs.get(), Ctx), cloneExpr(B->Rhs.get(), Ctx), B->Ty,
        B->Loc);
  }
  case VExpr::UnaryOp: {
    const auto *U = static_cast<const VUnaryOpExpr *>(E);
    return std::make_unique<VUnaryOpExpr>(
        U->Op, cloneExpr(U->Operand.get(), Ctx), U->Ty, U->Loc);
  }
  case VExpr::Cast: {
    const auto *C = static_cast<const VCastExpr *>(E);
    return std::make_unique<VCastExpr>(cloneExpr(C->Inner.get(), Ctx), C->FromTy,
                                       C->Ty, C->Loc);
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
    return std::make_unique<VLoadExpr>(cloneExpr(L->Ptr.get(), Ctx), L->Ty, L->Loc,
                                       Heap);
  }
  case VExpr::Result: {
    if (auto It = Ctx.Renames.find("result"); It != Ctx.Renames.end())
      return std::make_unique<VVarExpr>(It->second, E->Ty, E->Loc);
    return std::make_unique<VResultExpr>(E->Ty, E->Loc);
  }
  case VExpr::Old: {
    const auto *O = static_cast<const VOldExpr *>(E);
    CloneCtx Inner{Ctx.Renames, Ctx.OldState, true};
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
      Name = "base";
    Name += "." + F->Field;
    if (Ctx.UseOldState) {
      if (auto It = Ctx.OldState.find(Name); It != Ctx.OldState.end())
        return cloneExpr(It->second.get(), CloneCtx{Ctx.Renames, Ctx.OldState, false});
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
    return std::make_unique<VSpecCallExpr>(C->Callee, std::move(Args), C->Ty,
                                           C->Loc);
  }
  case VExpr::Forall:
  case VExpr::Exists: {
    const auto *Q = static_cast<const VQuantifiedExpr *>(E);
    auto Body = cloneExpr(Q->Body.get(), Ctx);
    return E->K == VExpr::Forall
               ? std::unique_ptr<VExpr>(std::make_unique<VForallExpr>(
                     Q->Binder, cloneExpr(Q->Lo.get(), Ctx),
                     cloneExpr(Q->Hi.get(), Ctx), std::move(Body), Q->Loc))
               : std::unique_ptr<VExpr>(std::make_unique<VExistsExpr>(
                     Q->Binder, cloneExpr(Q->Lo.get(), Ctx),
                     cloneExpr(Q->Hi.get(), Ctx), std::move(Body), Q->Loc));
  }
  }
  return nullptr;
}

static std::unique_ptr<VExpr> makeEq(std::unique_ptr<VExpr> L,
                                     std::unique_ptr<VExpr> R,
                                     SourceLocation Loc) {
  return std::make_unique<VBinOpExpr>(VBinOp::Eq, std::move(L), std::move(R),
                                      VType::makeBool(), Loc);
}

static bool sameLvalue(const VExpr *A, const VExpr *B) {
  if (!A || !B)
    return false;
  if (A->K == VExpr::Var && B->K == VExpr::Var)
    return static_cast<const VVarExpr *>(A)->Name ==
           static_cast<const VVarExpr *>(B)->Name;
  if (A->K == VExpr::Load && B->K == VExpr::Load)
    return sameLvalue(static_cast<const VLoadExpr *>(A)->Ptr.get(),
                    static_cast<const VLoadExpr *>(B)->Ptr.get());
  if (A->K == VExpr::Var && B->K == VExpr::Load)
    return sameLvalue(A, static_cast<const VLoadExpr *>(B)->Ptr.get());
  if (A->K == VExpr::Load && B->K == VExpr::Var)
    return sameLvalue(static_cast<const VLoadExpr *>(A)->Ptr.get(), B);
  return false;
}

static void collectDottedVars(const VExpr *E, std::set<std::string> &Out) {
  if (!E)
    return;
  if (E->K == VExpr::Var) {
    const auto &N = static_cast<const VVarExpr *>(E)->Name;
    if (N.find('.') != std::string::npos)
      Out.insert(N);
    return;
  }
  if (E->K == VExpr::BinOp) {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    collectDottedVars(B->Lhs.get(), Out);
    collectDottedVars(B->Rhs.get(), Out);
    return;
  }
  if (E->K == VExpr::UnaryOp)
    collectDottedVars(static_cast<const VUnaryOpExpr *>(E)->Operand.get(), Out);
  if (E->K == VExpr::Old)
    collectDottedVars(static_cast<const VOldExpr *>(E)->Inner.get(), Out);
  if (E->K == VExpr::Load)
    collectDottedVars(static_cast<const VLoadExpr *>(E)->Ptr.get(), Out);
  if (E->K == VExpr::FieldAccess) {
    const auto *F = static_cast<const VFieldAccessExpr *>(E);
    collectDottedVars(F->Base.get(), Out);
  }
}

static bool storeAllowedByModifies(
    const VStoreStmt &St,
    const std::vector<std::unique_ptr<VExpr>> &Modifies) {
  if (Modifies.empty())
    return true;
  for (const auto &M : Modifies)
    if (sameLvalue(St.Ptr.get(), M.get()))
      return true;
  return false;
}

static std::unique_ptr<VExpr>
substParams(const VExpr *E, const std::map<std::string, std::unique_ptr<VExpr>> &Map,
            const CloneCtx &Ctx) {
  if (!E)
    return nullptr;
  if (E->K == VExpr::Var) {
    const auto *V = static_cast<const VVarExpr *>(E);
    if (auto It = Map.find(V->Name); It != Map.end())
      return cloneExpr(It->second.get(), Ctx);
    return cloneExpr(E, Ctx);
  }
  if (E->K == VExpr::BinOp) {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    return std::make_unique<VBinOpExpr>(
        B->Op, substParams(B->Lhs.get(), Map, Ctx), substParams(B->Rhs.get(), Map, Ctx),
        B->Ty, B->Loc);
  }
  if (E->K == VExpr::UnaryOp) {
    const auto *U = static_cast<const VUnaryOpExpr *>(E);
    return std::make_unique<VUnaryOpExpr>(
        U->Op, substParams(U->Operand.get(), Map, Ctx), U->Ty, U->Loc);
  }
  if (E->K == VExpr::Load) {
    const auto *L = static_cast<const VLoadExpr *>(E);
    return std::make_unique<VLoadExpr>(substParams(L->Ptr.get(), Map, Ctx), L->Ty, L->Loc,
                                       L->HeapVar);
  }
  if (E->K == VExpr::Old) {
    const auto *O = static_cast<const VOldExpr *>(E);
    return std::make_unique<VOldExpr>(substParams(O->Inner.get(), Map, Ctx), O->Ty, O->Loc);
  }
  if (E->K == VExpr::Result) {
    if (auto It = Map.find("result"); It != Map.end())
      return cloneExpr(It->second.get(), Ctx);
    return std::make_unique<VResultExpr>(E->Ty, E->Loc);
  }
  if (E->K == VExpr::FieldAccess) {
    const auto *F = static_cast<const VFieldAccessExpr *>(E);
    return std::make_unique<VFieldAccessExpr>(substParams(F->Base.get(), Map, Ctx),
                                              F->Field, F->Ty, F->Loc);
  }
  return cloneExpr(E, Ctx);
}

class PassivizerImpl {
  std::map<std::string, int> Versions;
  std::map<std::string, std::unique_ptr<VExpr>> OldState;
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

public:
  PassivizerImpl(const VFunction &Fn, FunctionMap FnMap)
      : Fn(Fn), FnMap(std::move(FnMap)) {}

  PassiveProgram run() {
    PassiveProgram P;
    CloneCtx Ctx{{}, OldState, false};

    Versions[VHeapName] = 0;
    std::string Heap0 = versionedName(VHeapName);
    OldState[VHeapName] = std::make_unique<VVarExpr>(Heap0, VType::makePtr(), SourceLocation());

    std::map<std::string, std::string> Renames;
    Renames[VHeapName] = Heap0;

    for (const auto &Param : Fn.Params) {
      std::string V0 = versionedName(Param.first);
      OldState[Param.first] = std::make_unique<VVarExpr>(V0, Param.second, SourceLocation());
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
      OldState[FV] = std::make_unique<VVarExpr>(V0, VType::makeInt32(Fn.IntMode), SourceLocation());
      Renames[FV] = V0;
    }

    for (const auto &Pre : Fn.Preconditions) {
      CloneCtx PCtx{Renames, OldState, false};
      P.EntryAssumes.push_back(cloneExpr(Pre.get(), PCtx));
    }

    for (const auto &S : Fn.Body)
      processStmt(*S, P, Renames);

    if (auto It = Renames.find("result"); It != Renames.end())
      P.ResultVarName = It->second;

    for (const auto &Post : Fn.Postconditions) {
      CloneCtx PCtx{Renames, OldState, false};
      P.ExitAsserts.push_back(cloneExpr(Post.get(), PCtx));
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
    auto CalleeIt = FnMap.find(C.Callee);
    if (CalleeIt == FnMap.end())
      return;
    const VFunction *Callee = CalleeIt->second;
    if (Callee->IsSpec)
      return;
    CloneCtx Ctx{Renames, OldState, false};
    std::map<std::string, std::unique_ptr<VExpr>> ParamMap;
    for (unsigned I = 0; I < Callee->Params.size() && I < C.Args.size(); ++I)
      ParamMap[Callee->Params[I].first] = cloneVExpr(C.Args[I].get());
    std::string RetVer;
    if (!C.ResultTarget.empty()) {
      RetVer = bump(C.ResultTarget);
      Renames[C.ResultTarget] = RetVer;
      ParamMap["result"] =
          std::make_unique<VVarExpr>(RetVer, Callee->ReturnType, C.Loc);
    }
    for (const auto &Pre : Callee->Preconditions) {
      auto PS = std::make_unique<PassiveStmt>();
      PS->K = PassiveStmt::Assume;
      PS->Cond = substParams(Pre.get(), ParamMap, Ctx);
      P.Stmts.push_back(std::move(PS));
    }
    if (!Callee->Modifies.empty())
      Renames[VHeapName] = bump(VHeapName);
    for (const auto &Post : Callee->Postconditions) {
      auto PS = std::make_unique<PassiveStmt>();
      PS->K = PassiveStmt::Assume;
      PS->Cond = substParams(Post.get(), ParamMap, Ctx);
      P.Stmts.push_back(std::move(PS));
    }
  }

  void processStmt(const VStmt &S, PassiveProgram &P,
                   std::map<std::string, std::string> &Renames) {
    switch (S.K) {
    case VStmt::Assign: {
      const auto &A = static_cast<const VAssignStmt &>(S);
      CloneCtx Ctx{Renames, OldState, false};
      auto Val = cloneExpr(A.Value.get(), Ctx);
      std::string NewName = bump(A.Target);
      Renames[A.Target] = NewName;
      auto PS = std::make_unique<PassiveStmt>();
      PS->K = PassiveStmt::Assume;
      PS->Cond = makeEq(std::make_unique<VVarExpr>(NewName, Val->Ty, A.Loc),
                        std::move(Val), A.Loc);
      P.Stmts.push_back(std::move(PS));
      break;
    }
    case VStmt::Store: {
      const auto &St = static_cast<const VStoreStmt &>(S);
      if (!storeAllowedByModifies(St, Fn.Modifies)) {
        auto PS = std::make_unique<PassiveStmt>();
        PS->K = PassiveStmt::Assert;
        PS->Cond = std::make_unique<VLiteralExpr>(0, VType::makeBool(), St.Loc);
        P.Stmts.push_back(std::move(PS));
        break;
      }
      CloneCtx Ctx{Renames, OldState, false};
      auto Ptr = cloneExpr(St.Ptr.get(), Ctx);
      auto Val = cloneExpr(St.Value.get(), Ctx);
      std::string OldHeap = Renames[VHeapName];
      std::string NewHeap = bump(VHeapName);
      Renames[VHeapName] = NewHeap;
      auto PS = std::make_unique<PassiveStmt>();
      PS->K = PassiveStmt::Assume;
      PS->Cond = std::make_unique<VHeapStoreExpr>(
          OldHeap, NewHeap, std::move(Ptr), std::move(Val), St.Loc);
      P.Stmts.push_back(std::move(PS));
      break;
    }
    case VStmt::If: {
      const auto &I = static_cast<const VIfStmt &>(S);
      CloneCtx Ctx{Renames, OldState, false};
      auto Cond = cloneExpr(I.Cond.get(), Ctx);
      auto ThenRenames = Renames;
      auto ElseRenames = Renames;
      for (const auto &TS : I.Then)
        processStmt(*TS, P, ThenRenames);
      for (const auto &ES : I.Else)
        processStmt(*ES, P, ElseRenames);
      std::set<std::string> Changed;
      for (const auto &[Name, Ver] : ThenRenames) {
        if (Renames.count(Name) && Renames[Name] != Ver)
          Changed.insert(Name);
      }
      for (const auto &[Name, Ver] : ElseRenames) {
        if (Renames.count(Name) && Renames[Name] != Ver)
          Changed.insert(Name);
      }
      for (const std::string &Name : Changed) {
        auto ThenVal = std::make_unique<VVarExpr>(ThenRenames[Name],
                                                  VType::makeInt32(Fn.IntMode),
                                                  I.Loc);
        auto ElseVal = std::make_unique<VVarExpr>(ElseRenames[Name],
                                                  VType::makeInt32(Fn.IntMode),
                                                  I.Loc);
        std::string Merged = bump(Name);
        Renames[Name] = Merged;
        auto MergeExpr = std::make_unique<VConditionalExpr>(
            cloneExpr(Cond.get(), Ctx), std::move(ThenVal), std::move(ElseVal),
            VType::makeInt32(Fn.IntMode), I.Loc);
        auto PS = std::make_unique<PassiveStmt>();
        PS->K = PassiveStmt::Assume;
        PS->Cond = makeEq(std::make_unique<VVarExpr>(Merged, VType::makeInt32(Fn.IntMode), I.Loc),
                          std::move(MergeExpr), I.Loc);
        P.Stmts.push_back(std::move(PS));
      }
      break;
    }
    case VStmt::Return: {
      const auto &R = static_cast<const VReturnStmt &>(S);
      CloneCtx Ctx{Renames, OldState, false};
      const VExpr *RetVal = R.Value.get();
      while (RetVal && RetVal->K == VExpr::Cast)
        RetVal = static_cast<const VCastExpr *>(RetVal)->Inner.get();
      if (RetVal && RetVal->K == VExpr::Var) {
        const std::string &Src = static_cast<const VVarExpr *>(RetVal)->Name;
        std::set<std::string> PostFields;
        for (const auto &Post : Fn.Postconditions)
          collectDottedVars(Post.get(), PostFields);
        bool LinkedFields = false;
        for (const std::string &FV : PostFields) {
          if (FV.rfind("result.", 0) != 0)
            continue;
          std::string SrcField = Src + "." + FV.substr(7);
          std::string DstVer = bump(FV);
          Renames[FV] = DstVer;
          std::string SrcVer = SrcField;
          if (auto It = Renames.find(SrcField); It != Renames.end())
            SrcVer = It->second;
          auto PS = std::make_unique<PassiveStmt>();
          PS->K = PassiveStmt::Assume;
          PS->Cond = makeEq(
              std::make_unique<VVarExpr>(DstVer, VType::makeInt32(Fn.IntMode), R.Loc),
              std::make_unique<VVarExpr>(SrcVer, VType::makeInt32(Fn.IntMode), R.Loc),
              R.Loc);
          P.Stmts.push_back(std::move(PS));
          LinkedFields = true;
        }
        if (LinkedFields) {
          Renames["result"] = Renames.count("result.x") ? Renames["result.x"] : bump(ResultVar);
          break;
        }
      }
      std::unique_ptr<VExpr> Ret =
          R.Value ? cloneExpr(R.Value.get(), Ctx)
                  : std::make_unique<VLiteralExpr>(0, VType::makeInt32(Fn.IntMode), R.Loc);
      std::string RetVer = bump(ResultVar);
      Renames["result"] = RetVer;
      auto PS = std::make_unique<PassiveStmt>();
      PS->K = PassiveStmt::Assume;
      PS->Cond = makeEq(std::make_unique<VVarExpr>(RetVer, Ret->Ty, R.Loc),
                        std::move(Ret), R.Loc);
      P.Stmts.push_back(std::move(PS));
      break;
    }
    case VStmt::While: {
      const auto &W = static_cast<const VWhileStmt &>(S);
      CloneCtx Ctx{Renames, OldState, false};
      for (const auto &Inv : W.Invariants) {
        auto PS = std::make_unique<PassiveStmt>();
        PS->K = PassiveStmt::Assume;
        PS->Cond = cloneExpr(Inv.get(), Ctx);
        P.Stmts.push_back(std::move(PS));
      }
      auto PSCond = std::make_unique<PassiveStmt>();
      PSCond->K = PassiveStmt::Assume;
      PSCond->Cond = cloneExpr(W.Cond.get(), Ctx);
      P.Stmts.push_back(std::move(PSCond));
      auto BodyRenames = Renames;
      for (const auto &BS : W.Body)
        processStmt(*BS, P, BodyRenames);
      for (const auto &Inv : W.Invariants) {
        CloneCtx ACtx{BodyRenames, OldState, false};
        auto PS = std::make_unique<PassiveStmt>();
        PS->K = PassiveStmt::Assert;
        PS->Cond = cloneExpr(Inv.get(), ACtx);
        P.Stmts.push_back(std::move(PS));
      }
      auto NotC = std::make_unique<VUnaryOpExpr>(
          VUnaryOp::Not, cloneExpr(W.Cond.get(), Ctx), VType::makeBool(), W.Loc);
      auto PSExit = std::make_unique<PassiveStmt>();
      PSExit->K = PassiveStmt::Assume;
      std::unique_ptr<VExpr> ExitAss = std::move(NotC);
      for (const auto &Inv : W.Invariants)
        ExitAss = std::make_unique<VBinOpExpr>(
            VBinOp::And, std::move(ExitAss), cloneExpr(Inv.get(), Ctx),
            VType::makeBool(), W.Loc);
      PSExit->Cond = std::move(ExitAss);
      P.Stmts.push_back(std::move(PSExit));
      Renames = BodyRenames;
      break;
    }
    case VStmt::GhostBlock: {
      const auto &G = static_cast<const VGhostBlockStmt &>(S);
      for (const auto &BS : G.Body)
        processStmt(*BS, P, Renames);
      break;
    }
    case VStmt::ContractAssert: {
      const auto &A = static_cast<const VContractAssertStmt &>(S);
      CloneCtx Ctx{Renames, OldState, false};
      auto PS = std::make_unique<PassiveStmt>();
      PS->K = PassiveStmt::Assert;
      PS->Cond = cloneExpr(A.Cond.get(), Ctx);
      P.Stmts.push_back(std::move(PS));
      break;
    }
    case VStmt::RevealWithFuel:
    case VStmt::HideSpec:
    case VStmt::RevealSpec:
      break;
    case VStmt::Call:
      emitCallStmt(static_cast<const VCallStmt &>(S), P, Renames);
      break;
    default:
      break;
    }
  }
};

PassiveProgram Passivizer::run(const VFunction &Fn) {
  PassivizerImpl Impl(Fn, FnMap);
  return Impl.run();
}