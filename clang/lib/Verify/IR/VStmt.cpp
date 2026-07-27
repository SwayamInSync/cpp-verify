//===--- VStmt.cpp --------------------------------------------------------===//
#include "VStmt.h"

using namespace clang;
using namespace verify;

std::unique_ptr<VStmt> verify::cloneVStmt(const VStmt *S) {
  if (!S)
    return nullptr;
  switch (S->K) {
  case VStmt::Assign: {
    const auto &A = static_cast<const VAssignStmt &>(*S);
    return std::make_unique<VAssignStmt>(A.Target, cloneVExpr(A.Value.get()),
                                         A.Loc);
  }
  case VStmt::Store: {
    const auto &St = static_cast<const VStoreStmt &>(*S);
    return std::make_unique<VStoreStmt>(cloneVExpr(St.Ptr.get()),
                                        cloneVExpr(St.Value.get()), St.Loc);
  }
  case VStmt::Allocate: {
    const auto &A = static_cast<const VAllocateStmt &>(*S);
    return std::make_unique<VAllocateStmt>(
        A.Target, A.AllocatedType, A.AllocationIdentity,
        cloneVExpr(A.Initializer.get()), A.SizeBytes, A.AlignBytes, A.Loc);
  }
  case VStmt::Free: {
    const auto &F = static_cast<const VFreeStmt &>(*S);
    return std::make_unique<VFreeStmt>(cloneVExpr(F.Ptr.get()), F.Loc);
  }
  case VStmt::If: {
    const auto &I = static_cast<const VIfStmt &>(*S);
    std::vector<std::unique_ptr<VStmt>> Then, Else;
    for (const auto &T : I.Then)
      Then.push_back(cloneVStmt(T.get()));
    for (const auto &E : I.Else)
      Else.push_back(cloneVStmt(E.get()));
    return std::make_unique<VIfStmt>(cloneVExpr(I.Cond.get()), std::move(Then),
                                     std::move(Else), I.Loc);
  }
  case VStmt::While: {
    const auto &W = static_cast<const VWhileStmt &>(*S);
    std::vector<std::unique_ptr<VExpr>> Inv;
    for (const auto &I : W.Invariants)
      Inv.push_back(cloneVExpr(I.get()));
    std::vector<std::unique_ptr<VExpr>> Dec;
    for (const auto &D : W.Decreases)
      Dec.push_back(cloneVExpr(D.get()));
    std::vector<std::unique_ptr<VStmt>> Body;
    for (const auto &B : W.Body)
      Body.push_back(cloneVStmt(B.get()));
    return std::make_unique<VWhileStmt>(cloneVExpr(W.Cond.get()),
                                        std::move(Inv), std::move(Dec),
                                        std::move(Body), W.Loc);
  }
  case VStmt::Call: {
    const auto &C = static_cast<const VCallStmt &>(*S);
    std::vector<std::unique_ptr<VExpr>> Args;
    for (const auto &A : C.Args)
      Args.push_back(cloneVExpr(A.get()));
    return std::make_unique<VCallStmt>(C.Callee, C.CalleeIdentity,
                                       std::move(Args), C.ResultTarget, C.Loc,
                                       C.IsProofCall);
  }
  case VStmt::Assert: {
    const auto &A = static_cast<const VAssertStmt &>(*S);
    return std::make_unique<VAssertStmt>(cloneVExpr(A.Cond.get()), A.Loc);
  }
  case VStmt::Assume: {
    const auto &A = static_cast<const VAssumeStmt &>(*S);
    return std::make_unique<VAssumeStmt>(cloneVExpr(A.Cond.get()), A.Loc);
  }
  case VStmt::Return: {
    const auto &R = static_cast<const VReturnStmt &>(*S);
    return std::make_unique<VReturnStmt>(cloneVExpr(R.Value.get()), R.Loc);
  }
  case VStmt::Seq: {
    const auto &Seq = static_cast<const VSeqStmt &>(*S);
    std::vector<std::unique_ptr<VStmt>> Stmts;
    for (const auto &Nested : Seq.Stmts)
      Stmts.push_back(cloneVStmt(Nested.get()));
    return std::make_unique<VSeqStmt>(std::move(Stmts), Seq.Loc);
  }
  case VStmt::Havoc: {
    const auto &H = static_cast<const VHavocStmt &>(*S);
    return std::make_unique<VHavocStmt>(H.Target, H.Loc);
  }
  case VStmt::GhostBlock: {
    const auto &G = static_cast<const VGhostBlockStmt &>(*S);
    std::vector<std::unique_ptr<VStmt>> Body;
    for (const auto &B : G.Body)
      Body.push_back(cloneVStmt(B.get()));
    return std::make_unique<VGhostBlockStmt>(std::move(Body), G.Loc);
  }
  case VStmt::RevealWithFuel: {
    const auto &R = static_cast<const VRevealWithFuelStmt &>(*S);
    return std::make_unique<VRevealWithFuelStmt>(R.SpecFunction, R.Fuel, R.Loc);
  }
  case VStmt::HideSpec: {
    const auto &H = static_cast<const VHideSpecStmt &>(*S);
    return std::make_unique<VHideSpecStmt>(H.SpecFunction, H.Loc);
  }
  case VStmt::RevealSpec: {
    const auto &R = static_cast<const VRevealSpecStmt &>(*S);
    return std::make_unique<VRevealSpecStmt>(R.SpecFunction, R.Loc);
  }
  case VStmt::ContractAssert: {
    const auto &A = static_cast<const VContractAssertStmt &>(*S);
    return std::make_unique<VContractAssertStmt>(cloneVExpr(A.Cond.get()),
                                                 A.Loc);
  }
  }
  return nullptr;
}

VFunction verify::cloneVFunction(const VFunction &Fn) {
  VFunction Out;
  Out.Name = Fn.Name;
  Out.Identity = Fn.Identity;
  Out.ReturnType = Fn.ReturnType;
  Out.IntMode = Fn.IntMode;
  Out.IsSpec = Fn.IsSpec;
  Out.IsProof = Fn.IsProof;
  Out.IsConstexprSpec = Fn.IsConstexprSpec;
  Out.RequiresCallDefinedness = Fn.RequiresCallDefinedness;
  Out.IsExternalContract = Fn.IsExternalContract;
  Out.NeedsDecreasesCheck = Fn.NeedsDecreasesCheck;
  Out.UsesDynamicStorage = Fn.UsesDynamicStorage;
  Out.SpecFuel = Fn.SpecFuel;
  Out.HiddenSpecs = Fn.HiddenSpecs;
  Out.RevealedSpecs = Fn.RevealedSpecs;
  Out.Params = Fn.Params;
  Out.ReturnFields = Fn.ReturnFields;
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
  for (const auto &D : Fn.Decreases)
    Out.Decreases.push_back(cloneVExpr(D.get()));
  for (const auto &S : Fn.Body)
    Out.Body.push_back(cloneVStmt(S.get()));
  return Out;
}