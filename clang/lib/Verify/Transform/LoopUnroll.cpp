//===--- LoopUnroll.cpp ---------------------------------------------------===//
#include "LoopUnroll.h"

using namespace clang;
using namespace verify;

static std::vector<std::unique_ptr<VStmt>>
unrollStmts(const std::vector<std::unique_ptr<VStmt>> &Stmts, unsigned K);

static std::unique_ptr<VStmt> unrollWhile(const VWhileStmt &W, unsigned K) {
  if (K == 0) {
    auto NotCond = std::make_unique<VUnaryOpExpr>(
        VUnaryOp::Not, cloneVExpr(W.Cond.get()), VType::makeBool(), W.Loc);
    return std::make_unique<VAssertStmt>(std::move(NotCond), W.Loc);
  }

  auto Then = unrollStmts(W.Body, K);
  Then.push_back(unrollWhile(W, K - 1));
  return std::make_unique<VIfStmt>(cloneVExpr(W.Cond.get()), std::move(Then),
                                   std::vector<std::unique_ptr<VStmt>>{},
                                   W.Loc);
}

static std::vector<std::unique_ptr<VStmt>>
unrollStmts(const std::vector<std::unique_ptr<VStmt>> &Stmts, unsigned K) {
  std::vector<std::unique_ptr<VStmt>> Out;
  for (const auto &S : Stmts) {
    if (S->K == VStmt::While) {
      const auto &W = static_cast<const VWhileStmt &>(*S);
      Out.push_back(unrollWhile(W, K));
      continue;
    }
    if (S->K == VStmt::If) {
      const auto &I = static_cast<const VIfStmt &>(*S);
      auto Then = unrollStmts(I.Then, K);
      auto Else = unrollStmts(I.Else, K);
      Out.push_back(std::make_unique<VIfStmt>(
          cloneVExpr(I.Cond.get()), std::move(Then), std::move(Else), I.Loc));
      continue;
    }
    if (S->K == VStmt::Seq) {
      const auto &Seq = static_cast<const VSeqStmt &>(*S);
      auto Inner = unrollStmts(Seq.Stmts, K);
      Out.insert(Out.end(), std::make_move_iterator(Inner.begin()),
                 std::make_move_iterator(Inner.end()));
      continue;
    }
    switch (S->K) {
    case VStmt::Assign:
      Out.push_back(std::make_unique<VAssignStmt>(
          static_cast<const VAssignStmt &>(*S).Target,
          cloneVExpr(static_cast<const VAssignStmt &>(*S).Value.get()),
          S->Loc));
      break;
    case VStmt::Store:
      Out.push_back(std::make_unique<VStoreStmt>(
          cloneVExpr(static_cast<const VStoreStmt &>(*S).Ptr.get()),
          cloneVExpr(static_cast<const VStoreStmt &>(*S).Value.get()), S->Loc));
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
          static_cast<const VCallStmt &>(*S).IsProofCall));
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
  Out.RequiresCallDefinedness = Fn.RequiresCallDefinedness;
  Out.NeedsDecreasesCheck = Fn.NeedsDecreasesCheck;
  Out.IsExternalContract = Fn.IsExternalContract;
  Out.UsesDynamicStorage = Fn.UsesDynamicStorage;
  Out.Params = Fn.Params;
  Out.ReturnFields = Fn.ReturnFields;
  Out.ExplicitPreconditionCount = Fn.ExplicitPreconditionCount;
  for (const auto &P : Fn.Preconditions)
    Out.Preconditions.push_back(cloneVExpr(P.get()));
  for (const auto &P : Fn.Postconditions)
    Out.Postconditions.push_back(cloneVExpr(P.get()));
  for (const auto &R : Fn.Recommends)
    Out.Recommends.push_back(cloneVExpr(R.get()));
  for (const auto &M : Fn.Modifies)
    Out.Modifies.push_back(cloneVExpr(M.get()));
  for (const auto &A : Fn.Aliases)
    Out.Aliases.emplace_back(cloneVExpr(A.first.get()),
                             cloneVExpr(A.second.get()));
  for (const auto &Decrease : Fn.Decreases)
    Out.Decreases.push_back(cloneVExpr(Decrease.get()));
  Out.SpecFuel = Fn.SpecFuel;
  Out.HiddenSpecs = Fn.HiddenSpecs;
  Out.RevealedSpecs = Fn.RevealedSpecs;
  if (K == 0) {
    for (const auto &S : Fn.Body)
      Out.Body.push_back(cloneVStmt(S.get()));
    return Out;
  }
  Out.Body = unrollStmts(Fn.Body, K);
  return Out;
}