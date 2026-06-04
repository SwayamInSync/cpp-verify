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
  case VExpr::OverflowCheck: {
    const auto *O = static_cast<const VOverflowCheckExpr *>(E);
    return std::make_unique<VOverflowCheckExpr>(
        O->Op, cloneExpr(O->Lhs.get(), Ctx),
        O->Rhs ? cloneExpr(O->Rhs.get(), Ctx) : nullptr, O->Loc);
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

/// The base pointer an address/lvalue is rooted at: strips casts, pointer
/// arithmetic (`p + i` -> `p`), and dereferences (`*p`'s lvalue Load(p) -> `p`).
/// Returns a Var when the root is a named pointer, else the innermost expr.
static const VExpr *pointerBase(const VExpr *E) {
  if (!E)
    return nullptr;
  switch (E->K) {
  case VExpr::Cast:
    return pointerBase(static_cast<const VCastExpr *>(E)->Inner.get());
  case VExpr::Load:
    return pointerBase(static_cast<const VLoadExpr *>(E)->Ptr.get());
  case VExpr::BinOp: {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    if (B->Op == VBinOp::Add || B->Op == VBinOp::Sub) {
      // Pointer arithmetic: the base is whichever operand reduces to a pointer
      // Var (conventionally the left in `p + i`).
      if (const VExpr *L = pointerBase(B->Lhs.get()); L && L->K == VExpr::Var)
        return L;
      if (const VExpr *R = pointerBase(B->Rhs.get()); R && R->K == VExpr::Var)
        return R;
    }
    return E;
  }
  default:
    return E;
  }
}

/// Two addresses/lvalues are rooted at the same named pointer.
static bool sameBase(const VExpr *A, const VExpr *B) {
  const VExpr *PA = pointerBase(A);
  const VExpr *PB = pointerBase(B);
  return PA && PB && PA->K == VExpr::Var && PB->K == VExpr::Var &&
         static_cast<const VVarExpr *>(PA)->Name ==
             static_cast<const VVarExpr *>(PB)->Name;
}

static bool storeAllowedByModifies(
    const VStoreStmt &St,
    const std::vector<std::unique_ptr<VExpr>> &Modifies) {
  if (Modifies.empty())
    return true;
  for (const auto &M : Modifies)
    // Exact lvalue (`*p` matches `*p`), or region: a store through `*(p + i)`
    // is covered by `modifies(*p)` since `*p` denotes the whole region at `p`.
    if (sameLvalue(St.Ptr.get(), M.get()) || sameBase(St.Ptr.get(), M.get()))
      return true;
  return false;
}

/// Collect the program state a loop body may modify, so it can be havocked for
/// the inductive step / continuation: local variables assigned (directly or in
/// nested control flow) and whether the heap may change. Conservative — over-
/// approximating the modified set stays sound (it just havocs more).
static void collectLoopMods(const std::vector<std::unique_ptr<VStmt>> &Body,
                            const FunctionMap &FnMap,
                            std::set<std::string> &Locals, bool &HeapMod) {
  for (const auto &S : Body) {
    switch (S->K) {
    case VStmt::Assign:
      Locals.insert(static_cast<const VAssignStmt &>(*S).Target);
      break;
    case VStmt::Store:
      HeapMod = true;
      break;
    case VStmt::Call: {
      const auto &C = static_cast<const VCallStmt &>(*S);
      if (!C.ResultTarget.empty())
        Locals.insert(C.ResultTarget);
      auto It = FnMap.find(C.Callee);
      if (It == FnMap.end() || !It->second || !It->second->Modifies.empty())
        HeapMod = true; // unknown callee or one that writes through pointers
      break;
    }
    case VStmt::If: {
      const auto &I = static_cast<const VIfStmt &>(*S);
      collectLoopMods(I.Then, FnMap, Locals, HeapMod);
      collectLoopMods(I.Else, FnMap, Locals, HeapMod);
      break;
    }
    case VStmt::While:
      collectLoopMods(static_cast<const VWhileStmt &>(*S).Body, FnMap, Locals,
                      HeapMod);
      break;
    case VStmt::Seq:
      collectLoopMods(static_cast<const VSeqStmt &>(*S).Stmts, FnMap, Locals,
                      HeapMod);
      break;
    default:
      // Ghost/proof/assert/assume statements do not modify real program state.
      break;
    }
  }
}

/// Build the lexicographic termination assertion for a decreases tuple:
///   lexLess(New, Old) && (New[i] >= 0 for every i)
/// where lexLess((a..),(b..)) = OR_j ( AND_{i<j} a_i == b_i  &&  a_j < b_j ).
/// Requiring every component non-negative makes the order well-founded over the
/// naturals. For a single-element tuple this is exactly `0 <= a < b`.
static std::unique_ptr<VExpr>
buildLexDecrease(std::vector<std::unique_ptr<VExpr>> New,
                 std::vector<std::unique_ptr<VExpr>> Old, VType IntTy,
                 SourceLocation Loc) {
  auto Bool = [] { return VType::makeBool(); };
  auto bin = [&](VBinOp Op, std::unique_ptr<VExpr> L, std::unique_ptr<VExpr> R) {
    return std::make_unique<VBinOpExpr>(Op, std::move(L), std::move(R), Bool(),
                                        Loc);
  };
  unsigned K = New.size();

  // lexLess as a disjunction over the position j that strictly decreases.
  std::unique_ptr<VExpr> Lex;
  for (unsigned j = 0; j < K; ++j) {
    std::unique_ptr<VExpr> EqPrefix;
    for (unsigned i = 0; i < j; ++i) {
      auto Eq = bin(VBinOp::Eq, cloneVExpr(New[i].get()), cloneVExpr(Old[i].get()));
      EqPrefix = EqPrefix ? bin(VBinOp::And, std::move(EqPrefix), std::move(Eq))
                          : std::move(Eq);
    }
    auto Lt = bin(VBinOp::Lt, cloneVExpr(New[j].get()), cloneVExpr(Old[j].get()));
    auto Disjunct = EqPrefix ? bin(VBinOp::And, std::move(EqPrefix), std::move(Lt))
                             : std::move(Lt);
    Lex = Lex ? bin(VBinOp::Or, std::move(Lex), std::move(Disjunct))
              : std::move(Disjunct);
  }

  // Every new component non-negative.
  std::unique_ptr<VExpr> NonNeg;
  for (unsigned i = 0; i < K; ++i) {
    auto Ge = bin(VBinOp::Ge, cloneVExpr(New[i].get()),
                  std::make_unique<VLiteralExpr>(0, IntTy, Loc));
    NonNeg = NonNeg ? bin(VBinOp::And, std::move(NonNeg), std::move(Ge))
                    : std::move(Ge);
  }

  return bin(VBinOp::And, std::move(Lex), std::move(NonNeg));
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

  /// Single SSA name that holds the function's return value across *all* return
  /// sites. Each return contributes a path-guarded `live -> result == retval`
  /// assumption, so the post-condition (checked once, against this name) sees
  /// the correct value on every path — including early returns.
  std::string ResultFinalVar;
  const VFunction &Fn;
  FunctionMap FnMap;

  std::string versionedName(const std::string &N) {
    int &V = Versions[N];
    return N + "_" + std::to_string(V);
  }

  std::string bump(const std::string &N) {
    return N + "_" + std::to_string(++Versions[N]);
  }

  /// Path condition of the branches currently being passivized.
  std::vector<std::unique_ptr<VExpr>> GuardStack;

  /// Path conditions under which an early `return` has already fired. Code that
  /// textually follows the enclosing branch is only *reached* when none of these
  /// held, so its asserts/assumes must be guarded by their negation. Without
  /// this, a loop placed after `if (n <= 1) return n;` would have its
  /// establishment `assert(I)` checked even for `n <= 1` (where the loop is
  /// never entered), producing a spurious failure.
  std::vector<std::unique_ptr<VExpr>> DeadConds;

  /// Wrap an assertion/assumption condition with the current "still executing"
  /// path condition, so that something emitted inside conditional branches
  /// (e.g. a callee precondition for a call under `if (c)`, or a loop's
  /// invariant after an early return) only needs to hold on the path that
  /// actually reaches it: returns `(live ? Cond : true)` where
  /// `live = (g1 && g2 && ...) && !dead1 && !dead2 && ...`.
  std::unique_ptr<VExpr> guardCond(std::unique_ptr<VExpr> Cond,
                                   SourceLocation Loc) {
    if (GuardStack.empty() && DeadConds.empty())
      return Cond;
    std::unique_ptr<VExpr> Conj;
    auto conjoin = [&](std::unique_ptr<VExpr> E) {
      Conj = Conj ? std::make_unique<VBinOpExpr>(VBinOp::And, std::move(Conj),
                                                 std::move(E), VType::makeBool(),
                                                 Loc)
                  : std::move(E);
    };
    for (const auto &G : GuardStack)
      conjoin(cloneVExpr(G.get()));
    for (const auto &D : DeadConds)
      conjoin(std::make_unique<VUnaryOpExpr>(
          VUnaryOp::Not, cloneVExpr(D.get()), VType::makeBool(), Loc));
    auto True = std::make_unique<VLiteralExpr>(1, VType::makeBool(), Loc);
    return std::make_unique<VConditionalExpr>(std::move(Conj), std::move(Cond),
                                              std::move(True), VType::makeBool(),
                                              Loc);
  }

  /// Record that an (early) return fires under the current branch path, so
  /// everything after the enclosing branch is guarded by its negation.
  void recordReturnGuard(SourceLocation Loc) {
    if (GuardStack.empty())
      return;
    std::unique_ptr<VExpr> Conj;
    for (const auto &G : GuardStack) {
      auto GC = cloneVExpr(G.get());
      Conj = Conj ? std::make_unique<VBinOpExpr>(VBinOp::And, std::move(Conj),
                                                 std::move(GC), VType::makeBool(),
                                                 Loc)
                  : std::move(GC);
    }
    DeadConds.push_back(std::move(Conj));
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
    // Modular protocol: the caller must *establish* the callee's precondition,
    // so assert it (not assume). Assuming it here would let any call silently
    // satisfy its own precondition, which is unsound.
    for (const auto &Pre : Callee->Preconditions) {
      auto PS = std::make_unique<PassiveStmt>();
      PS->K = PassiveStmt::Assert;
      PS->Cond = guardCond(substParams(Pre.get(), ParamMap, Ctx), C.Loc);
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
      // Hoist Val->Ty before the move: argument evaluation order is unspecified.
      VType ValTy = Val->Ty;
      PS->Cond = makeEq(std::make_unique<VVarExpr>(NewName, ValTy, A.Loc),
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
      GuardStack.push_back(cloneVExpr(Cond.get()));
      for (const auto &TS : I.Then)
        processStmt(*TS, P, ThenRenames);
      GuardStack.pop_back();
      GuardStack.push_back(std::make_unique<VUnaryOpExpr>(
          VUnaryOp::Not, cloneVExpr(Cond.get()), VType::makeBool(), I.Loc));
      for (const auto &ES : I.Else)
        processStmt(*ES, P, ElseRenames);
      GuardStack.pop_back();
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
          PS->Cond = guardCond(
              makeEq(std::make_unique<VVarExpr>(DstVer, VType::makeInt32(Fn.IntMode), R.Loc),
                     std::make_unique<VVarExpr>(SrcVer, VType::makeInt32(Fn.IntMode), R.Loc),
                     R.Loc),
              R.Loc);
          P.Stmts.push_back(std::move(PS));
          LinkedFields = true;
        }
        if (LinkedFields) {
          Renames["result"] = Renames.count("result.x") ? Renames["result.x"] : bump(ResultVar);
          recordReturnGuard(R.Loc);
          break;
        }
      }
      std::unique_ptr<VExpr> Ret =
          R.Value ? cloneExpr(R.Value.get(), Ctx)
                  : std::make_unique<VLiteralExpr>(0, VType::makeInt32(Fn.IntMode), R.Loc);
      // One result name shared by all returns; each return constrains it only on
      // its own live path, so the post-condition reads the right value even when
      // an earlier `return` already fired (see ResultFinalVar / DeadConds).
      if (ResultFinalVar.empty())
        ResultFinalVar = bump(ResultVar);
      Renames["result"] = ResultFinalVar;
      auto PS = std::make_unique<PassiveStmt>();
      PS->K = PassiveStmt::Assume;
      // Read Ret->Ty into a local first: passing both `Ret->Ty` and
      // `std::move(Ret)` as arguments to the same call is unsequenced, so a
      // compiler that evaluates the move first nulls `Ret` before the
      // dereference (crashes under GCC's right-to-left argument evaluation).
      VType RetTy = Ret->Ty;
      PS->Cond = guardCond(
          makeEq(std::make_unique<VVarExpr>(ResultFinalVar, RetTy, R.Loc),
                 std::move(Ret), R.Loc),
          R.Loc);
      P.Stmts.push_back(std::move(PS));
      // Mark this path as returned *after* its own guarded assume, so the guard
      // above still covers this return's path while later code excludes it.
      recordReturnGuard(R.Loc);
      break;
    }
    case VStmt::While: {
      // Sound havoc/assume/assert encoding (ARCHITECTURE.md):
      //   1. assert(I)              -- establishment, from the concrete pre-state
      //   2. havoc(modified + heap) -- forget loop-modified state
      //   3. assume(I)              -- inductive hypothesis (arbitrary state)
      //   4. assume(cond); body; assert(I); assert(D decreases)  -- preservation
      //                                                              + termination
      //   5. havoc again; assume(I && !cond)  -- continuation
      // The body's iteration (under cond) and the continuation (under !cond) use
      // *distinct* havocked SSA versions, so they never contradict in the linear
      // passive program.
      const auto &W = static_cast<const VWhileStmt &>(S);

      std::set<std::string> Mods;
      bool HeapMod = false;
      collectLoopMods(W.Body, FnMap, Mods, HeapMod);

      // Guard every invariant assume/assert with the live path condition: a
      // loop after an early `return` is only entered when that return did not
      // fire, so its establishment/preservation/termination obligations (and
      // the inductive-hypothesis assumptions, which would otherwise be
      // vacuously contradictory off-path and poison later asserts) must be
      // gated by `live`.
      auto emit = [&](PassiveStmt::Kind K, std::unique_ptr<VExpr> C) {
        auto PS = std::make_unique<PassiveStmt>();
        PS->K = K;
        PS->Cond = guardCond(std::move(C), W.Loc);
        P.Stmts.push_back(std::move(PS));
      };
      auto havoc = [&]() {
        for (const std::string &V : Mods)
          Renames[V] = bump(V);
        if (HeapMod)
          Renames[VHeapName] = bump(VHeapName);
      };

      // (1) Establishment: the invariant must hold when the loop is reached.
      {
        CloneCtx C{Renames, OldState, false};
        for (const auto &Inv : W.Invariants)
          emit(PassiveStmt::Assert, cloneExpr(Inv.get(), C));
      }

      // (2)-(4) Inductive step on an arbitrary state satisfying the invariant.
      havoc();
      {
        CloneCtx C{Renames, OldState, false};
        for (const auto &Inv : W.Invariants)
          emit(PassiveStmt::Assume, cloneExpr(Inv.get(), C));
        // Snapshot the (lexicographic) measure on entry to the iteration.
        std::vector<std::unique_ptr<VExpr>> DecOld;
        for (const auto &D : W.Decreases)
          DecOld.push_back(cloneExpr(D.get(), C));
        emit(PassiveStmt::Assume, cloneExpr(W.Cond.get(), C));

        auto BodyRenames = Renames;
        for (const auto &BS : W.Body)
          processStmt(*BS, P, BodyRenames);

        CloneCtx BC{BodyRenames, OldState, false};
        for (const auto &Inv : W.Invariants)
          emit(PassiveStmt::Assert, cloneExpr(Inv.get(), BC)); // preservation
        if (!W.Decreases.empty()) {
          // Lexicographic strict decrease, each component bounded below by 0.
          VType IntTy = VType::makeInt32(Fn.IntMode);
          std::vector<std::unique_ptr<VExpr>> DecNew;
          for (const auto &D : W.Decreases)
            DecNew.push_back(cloneExpr(D.get(), BC));
          emit(PassiveStmt::Assert,
               buildLexDecrease(std::move(DecNew), std::move(DecOld), IntTy,
                                W.Loc));
        }
      }

      // (5) Continuation: a fresh arbitrary state with the invariant and !cond.
      havoc();
      {
        CloneCtx C{Renames, OldState, false};
        for (const auto &Inv : W.Invariants)
          emit(PassiveStmt::Assume, cloneExpr(Inv.get(), C));
        emit(PassiveStmt::Assume,
             std::make_unique<VUnaryOpExpr>(VUnaryOp::Not,
                                            cloneExpr(W.Cond.get(), C),
                                            VType::makeBool(), W.Loc));
      }
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
      // Guard by the live path condition: a contract_assert inside a branch (or
      // after an early return) only needs to hold on the path that reaches it.
      PS->Cond = guardCond(cloneExpr(A.Cond.get(), Ctx), A.Loc);
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