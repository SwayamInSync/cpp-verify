//===--- LoopUnroll.cpp ---------------------------------------------------===//
#include "LoopUnroll.h"

using namespace clang;
using namespace verify;

static std::vector<std::unique_ptr<VStmt>>
unrollStmts(const std::vector<std::unique_ptr<VStmt>> &Stmts, unsigned K);

static std::vector<std::unique_ptr<VStmt>>
unrollStmts(const std::vector<std::unique_ptr<VStmt>> &Stmts, unsigned K) {
  std::vector<std::unique_ptr<VStmt>> Out;
  for (const auto &S : Stmts) {
    if (S->K == VStmt::While) {
      const auto &W = static_cast<const VWhileStmt &>(*S);
      for (unsigned I = 0; I < K; ++I) {
        Out.push_back(std::make_unique<VAssumeStmt>(
            cloneVExpr(W.Cond.get()), W.Loc));
        auto Body = unrollStmts(W.Body, K);
        Out.insert(Out.end(), std::make_move_iterator(Body.begin()),
                   std::make_move_iterator(Body.end()));
      }
      auto NotCond = std::make_unique<VUnaryOpExpr>(
          VUnaryOp::Not, cloneVExpr(W.Cond.get()), VType::makeBool(), W.Loc);
      Out.push_back(
          std::make_unique<VAssumeStmt>(std::move(NotCond), W.Loc));
      continue;
    }
    if (S->K == VStmt::If) {
      const auto &I = static_cast<const VIfStmt &>(*S);
      auto Then = unrollStmts(I.Then, K);
      auto Else = unrollStmts(I.Else, K);
      Out.push_back(std::make_unique<VIfStmt>(cloneVExpr(I.Cond.get()),
                                              std::move(Then), std::move(Else),
                                              I.Loc));
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
          [&] {
            std::vector<std::unique_ptr<VExpr>> Args;
            for (const auto &A : static_cast<const VCallStmt &>(*S).Args)
              Args.push_back(cloneVExpr(A.get()));
            return Args;
          }(),
          static_cast<const VCallStmt &>(*S).ResultTarget, S->Loc));
      break;
    case VStmt::Return:
      Out.push_back(std::make_unique<VReturnStmt>(
          cloneVExpr(static_cast<const VReturnStmt &>(*S).Value.get()), S->Loc));
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
  Out.ReturnType = Fn.ReturnType;
  Out.IntMode = Fn.IntMode;
  Out.Params = Fn.Params;
  for (const auto &P : Fn.Preconditions)
    Out.Preconditions.push_back(cloneVExpr(P.get()));
  for (const auto &P : Fn.Postconditions)
    Out.Postconditions.push_back(cloneVExpr(P.get()));
  for (const auto &R : Fn.Recommends)
    Out.Recommends.push_back(cloneVExpr(R.get()));
  for (const auto &M : Fn.Modifies)
    Out.Modifies.push_back(cloneVExpr(M.get()));
  for (const auto &A : Fn.Aliases)
    Out.Aliases.emplace_back(cloneVExpr(A.first.get()), cloneVExpr(A.second.get()));
  if (K == 0) {
    for (const auto &S : Fn.Body)
      Out.Body.push_back(cloneVStmt(S.get()));
    return Out;
  }
  Out.Body = unrollStmts(Fn.Body, K);
  return Out;
}