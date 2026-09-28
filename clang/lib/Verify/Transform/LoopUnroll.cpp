//===--- LoopUnroll.cpp ---------------------------------------------------===//
#include "LoopUnroll.h"
#include <algorithm>

using namespace clang;
using namespace verify;

namespace {
/// Break and continue flags of the loop being unrolled.
struct ExitFlags {
  std::string Break;
  std::string Continue;
};
} // namespace

static std::vector<std::unique_ptr<VStmt>>
unrollRange(const std::vector<std::unique_ptr<VStmt>> &Stmts, size_t Begin,
            unsigned K, const ExitFlags *Flags, unsigned &NextLoop);

static std::vector<std::unique_ptr<VStmt>>
unrollStmts(const std::vector<std::unique_ptr<VStmt>> &Stmts, unsigned K,
            const ExitFlags *Flags, unsigned &NextLoop) {
  return unrollRange(Stmts, 0, K, Flags, NextLoop);
}

/// Whether S leaves the enclosing loop, not counting loops nested in S.
static bool exitsLoop(const VStmt &S) {
  auto any = [](const std::vector<std::unique_ptr<VStmt>> &Stmts) {
    return std::any_of(Stmts.begin(), Stmts.end(),
                       [](const auto &Nested) { return exitsLoop(*Nested); });
  };
  switch (S.K) {
  case VStmt::Break:
  case VStmt::Continue:
    return true;
  case VStmt::If: {
    const auto &I = static_cast<const VIfStmt &>(S);
    return any(I.Then) || any(I.Else);
  }
  case VStmt::Seq:
    return any(static_cast<const VSeqStmt &>(S).Stmts);
  case VStmt::GhostBlock:
    return any(static_cast<const VGhostBlockStmt &>(S).Body);
  default:
    return false;
  }
}

static std::unique_ptr<VExpr> flag(const std::string &Name,
                                   SourceLocation Loc) {
  return std::make_unique<VVarExpr>(Name, VType::makeBool(), Loc);
}

static std::unique_ptr<VStmt> setFlag(const std::string &Name, bool Value,
                                      SourceLocation Loc) {
  return std::make_unique<VAssignStmt>(
      Name,
      std::make_unique<VLiteralExpr>(Value ? 1 : 0, VType::makeBool(), Loc),
      Loc);
}

static std::unique_ptr<VExpr> negate(std::unique_ptr<VExpr> E,
                                     SourceLocation Loc) {
  return std::make_unique<VUnaryOpExpr>(VUnaryOp::Not, std::move(E),
                                        VType::makeBool(), Loc);
}

static std::unique_ptr<VStmt> unrollIteration(const VWhileStmt &W, unsigned K,
                                              unsigned Iteration,
                                              const ExitFlags *Flags,
                                              unsigned &NextLoop) {
  if (K == 0) {
    auto NotCond = std::make_unique<VUnaryOpExpr>(
        VUnaryOp::Not, cloneVExpr(W.Cond.get()), VType::makeBool(), W.Loc);
    std::vector<std::unique_ptr<VStmt>> Boundary;
    Boundary.push_back(std::make_unique<VAssertStmt>(
        cloneVExpr(NotCond.get()), W.Loc, ProofObligationKind::Unwinding));
    Boundary.push_back(
        std::make_unique<VAssumeStmt>(std::move(NotCond), W.Loc));
    auto Seq = std::make_unique<VSeqStmt>(std::move(Boundary), W.Loc);
    if (!Flags)
      return Seq;
    std::vector<std::unique_ptr<VStmt>> Guarded;
    Guarded.push_back(std::move(Seq));
    return std::make_unique<VIfStmt>(
        negate(flag(Flags->Break, W.Loc), W.Loc), std::move(Guarded),
        std::vector<std::unique_ptr<VStmt>>{}, W.Loc);
  }

  std::vector<std::unique_ptr<VStmt>> Then;
  if (Flags)
    Then.push_back(setFlag(Flags->Continue, false, W.Loc));
  auto Body = unrollStmts(W.Body, K, Flags, NextLoop);
  Then.insert(Then.end(), std::make_move_iterator(Body.begin()),
              std::make_move_iterator(Body.end()));
  Then.push_back(unrollIteration(W, K - 1, Iteration + 1, Flags, NextLoop));
  auto Iterate = std::make_unique<VIfStmt>(
      cloneVExpr(W.Cond.get()), std::move(Then),
      std::vector<std::unique_ptr<VStmt>>{}, W.Loc, true, Iteration);
  if (!Flags)
    return Iterate;
  // After a break the condition is not evaluated again.
  std::vector<std::unique_ptr<VStmt>> Guarded;
  Guarded.push_back(std::move(Iterate));
  return std::make_unique<VIfStmt>(
      negate(flag(Flags->Break, W.Loc), W.Loc), std::move(Guarded),
      std::vector<std::unique_ptr<VStmt>>{}, W.Loc);
}

static std::unique_ptr<VStmt> unrollWhile(const VWhileStmt &W, unsigned K,
                                          unsigned &NextLoop) {
  const bool HasExits =
      std::any_of(W.Body.begin(), W.Body.end(),
                  [](const auto &Nested) { return exitsLoop(*Nested); });
  if (!HasExits)
    return unrollIteration(W, K, 1, nullptr, NextLoop);
  const std::string Id = std::to_string(NextLoop++);
  const ExitFlags Flags{"__cppverify_break_" + Id,
                        "__cppverify_continue_" + Id};
  std::vector<std::unique_ptr<VStmt>> Out;
  Out.push_back(setFlag(Flags.Break, false, W.Loc));
  Out.push_back(unrollIteration(W, K, 1, &Flags, NextLoop));
  return std::make_unique<VSeqStmt>(std::move(Out), W.Loc);
}

static std::vector<std::unique_ptr<VStmt>>
unrollRange(const std::vector<std::unique_ptr<VStmt>> &Stmts, size_t Begin,
            unsigned K, const ExitFlags *Flags, unsigned &NextLoop) {
  std::vector<std::unique_ptr<VStmt>> Out;
  for (size_t Index = Begin; Index < Stmts.size(); ++Index) {
    const auto &S = Stmts[Index];
    if (Flags && (S->K == VStmt::Break || S->K == VStmt::Continue)) {
      Out.push_back(setFlag(
          S->K == VStmt::Break ? Flags->Break : Flags->Continue, true, S->Loc));
      return Out;
    }
    const bool MayExit = Flags && exitsLoop(*S);
    if (S->K == VStmt::While) {
      const auto &W = static_cast<const VWhileStmt &>(*S);
      Out.push_back(unrollWhile(W, K, NextLoop));
    } else if (S->K == VStmt::If) {
      const auto &I = static_cast<const VIfStmt &>(*S);
      auto Then = unrollStmts(I.Then, K, Flags, NextLoop);
      auto Else = unrollStmts(I.Else, K, Flags, NextLoop);
      Out.push_back(std::make_unique<VIfStmt>(
          cloneVExpr(I.Cond.get()), std::move(Then), std::move(Else), I.Loc,
          I.IsLoopUnroll, I.LoopUnrollIteration));
    } else if (S->K == VStmt::Seq) {
      const auto &Seq = static_cast<const VSeqStmt &>(*S);
      auto Inner = unrollStmts(Seq.Stmts, K, Flags, NextLoop);
      Out.insert(Out.end(), std::make_move_iterator(Inner.begin()),
                 std::make_move_iterator(Inner.end()));
    } else {
      switch (S->K) {
      case VStmt::Assign: {
        const auto &Assign = static_cast<const VAssignStmt &>(*S);
        Out.push_back(std::make_unique<VAssignStmt>(
            Assign.Target, cloneVExpr(Assign.Value.get()), S->Loc,
            Assign.IsReferenceBinding));
        break;
      }
      case VStmt::Store:
        Out.push_back(std::make_unique<VStoreStmt>(
            cloneVExpr(static_cast<const VStoreStmt &>(*S).Ptr.get()),
            cloneVExpr(static_cast<const VStoreStmt &>(*S).Value.get()), S->Loc,
            cloneVExpr(
                static_cast<const VStoreStmt &>(*S).AccessCondition.get())));
        break;
      case VStmt::Call:
        Out.push_back(std::make_unique<VCallStmt>(
            static_cast<const VCallStmt &>(*S).Callee,
            static_cast<const VCallStmt &>(*S).CalleeIdentity,
            [&] {
              std::vector<std::unique_ptr<VExpr>> Args;
              for (const auto &A : static_cast<const VCallStmt &>(*S).Args)
                Args.push_back(cloneVExpr(A.get()));
              return Args;
            }(),
            static_cast<const VCallStmt &>(*S).ResultTarget, S->Loc,
            static_cast<const VCallStmt &>(*S).IsProofCall,
            static_cast<const VCallStmt &>(*S).ResultProvenanceTarget));
        break;
      case VStmt::Return:
        Out.push_back(std::make_unique<VReturnStmt>(
            cloneVExpr(static_cast<const VReturnStmt &>(*S).Value.get()),
            S->Loc));
        break;
      default:
        Out.push_back(cloneVStmt(S.get()));
        break;
      }
    }
    // Statements after a possible exit run only while the iteration goes on.
    if (MayExit && Index + 1 < Stmts.size()) {
      auto Rest = unrollRange(Stmts, Index + 1, K, Flags, NextLoop);
      auto Continuing =
          negate(std::make_unique<VBinOpExpr>(
                     VBinOp::Or, flag(Flags->Break, S->Loc),
                     flag(Flags->Continue, S->Loc), VType::makeBool(), S->Loc),
                 S->Loc);
      Out.push_back(std::make_unique<VIfStmt>(
          std::move(Continuing), std::move(Rest),
          std::vector<std::unique_ptr<VStmt>>{}, S->Loc));
      return Out;
    }
  }
  return Out;
}

VFunction LoopUnroller::unroll(const VFunction &Fn, unsigned K) {
  VFunction Out;
  Out.Name = Fn.Name;
  Out.Identity = Fn.Identity;
  Out.ReturnType = Fn.ReturnType;
  Out.IntMode = Fn.IntMode;
  Out.IsSpec = Fn.IsSpec;
  Out.IsProof = Fn.IsProof;
  Out.IsConstexprSpec = Fn.IsConstexprSpec;
  Out.ReadsHeap = Fn.ReadsHeap;
  Out.RequiresCallDefinedness = Fn.RequiresCallDefinedness;
  Out.NeedsDecreasesCheck = Fn.NeedsDecreasesCheck;
  Out.IsExternalContract = Fn.IsExternalContract;
  Out.UsesDynamicStorage = Fn.UsesDynamicStorage;
  Out.FreshOwnedReturn = Fn.FreshOwnedReturn;
  Out.Params = Fn.Params;
  Out.SourceVariables = Fn.SourceVariables;
  Out.ReferenceParams = Fn.ReferenceParams;
  Out.ReturnFields = Fn.ReturnFields;
  Out.ExplicitPreconditionCount = Fn.ExplicitPreconditionCount;
  for (const auto &P : Fn.Preconditions)
    Out.Preconditions.push_back(cloneVExpr(P.get()));
  for (const auto &P : Fn.Postconditions)
    Out.Postconditions.push_back(cloneVExpr(P.get()));
  Out.PreconditionKinds = Fn.PreconditionKinds;
  Out.PostconditionKinds = Fn.PostconditionKinds;
  for (const auto &R : Fn.Recommends)
    Out.Recommends.push_back(cloneVExpr(R.get()));
  for (const auto &M : Fn.Modifies)
    Out.Modifies.push_back(cloneVExpr(M.get()));
  for (const auto &A : Fn.Aliases)
    Out.Aliases.emplace_back(cloneVExpr(A.first.get()),
                             cloneVExpr(A.second.get()));
  for (const auto &Extent : Fn.ValidExtents)
    Out.ValidExtents.emplace_back(Extent.Base, Extent.PointerType,
                                  cloneVExpr(Extent.Length.get()));
  Out.DisjointAddresses = Fn.DisjointAddresses;
  for (const auto &Decrease : Fn.Decreases)
    Out.Decreases.push_back(cloneVExpr(Decrease.get()));
  Out.SpecFuel = Fn.SpecFuel;
  Out.HiddenSpecs = Fn.HiddenSpecs;
  Out.RevealedSpecs = Fn.RevealedSpecs;
  Out.Layouts = Fn.Layouts;
  unsigned NextLoop = 0;
  Out.Body = unrollStmts(Fn.Body, K, nullptr, NextLoop);
  return Out;
}