//===--- VStmt.h - Layer 1 statements for CppVerify -------------*- C++ -*-===//
#ifndef LLVM_CLANG_VERIFY_IR_VSTMT_H
#define LLVM_CLANG_VERIFY_IR_VSTMT_H

#include "VExpr.h"
#include <map>
#include <memory>
#include <set>
#include <string>
#include <utility>
#include <vector>

namespace clang {
namespace verify {

class VStmt {
public:
  enum Kind {
    Assign,
    Store,
    If,
    While,
    Call,
    Assert,
    Assume,
    Return,
    Seq,
    Havoc,
    GhostBlock,
    RevealWithFuel,
    HideSpec,
    RevealSpec,
    ContractAssert
  };

  Kind K;
  SourceLocation Loc;
  virtual ~VStmt() = default;

protected:
  VStmt(Kind K, SourceLocation Loc) : K(K), Loc(Loc) {}
};

struct VAssignStmt : VStmt {
  std::string Target;
  std::unique_ptr<VExpr> Value;
  VAssignStmt(std::string T, std::unique_ptr<VExpr> V, SourceLocation Loc)
      : VStmt(Assign, Loc), Target(std::move(T)), Value(std::move(V)) {}
};

struct VStoreStmt : VStmt {
  std::unique_ptr<VExpr> Ptr;
  std::unique_ptr<VExpr> Value;
  VStoreStmt(std::unique_ptr<VExpr> P, std::unique_ptr<VExpr> V,
             SourceLocation Loc)
      : VStmt(Store, Loc), Ptr(std::move(P)), Value(std::move(V)) {}
};

struct VIfStmt : VStmt {
  std::unique_ptr<VExpr> Cond;
  std::vector<std::unique_ptr<VStmt>> Then;
  std::vector<std::unique_ptr<VStmt>> Else;
  VIfStmt(std::unique_ptr<VExpr> C, std::vector<std::unique_ptr<VStmt>> T,
          std::vector<std::unique_ptr<VStmt>> E, SourceLocation Loc)
      : VStmt(If, Loc), Cond(std::move(C)), Then(std::move(T)),
        Else(std::move(E)) {}
};

struct VAssertStmt : VStmt {
  std::unique_ptr<VExpr> Cond;
  VAssertStmt(std::unique_ptr<VExpr> C, SourceLocation Loc)
      : VStmt(Assert, Loc), Cond(std::move(C)) {}
};

struct VAssumeStmt : VStmt {
  std::unique_ptr<VExpr> Cond;
  VAssumeStmt(std::unique_ptr<VExpr> C, SourceLocation Loc)
      : VStmt(Assume, Loc), Cond(std::move(C)) {}
};

struct VReturnStmt : VStmt {
  std::unique_ptr<VExpr> Value;
  VReturnStmt(std::unique_ptr<VExpr> V, SourceLocation Loc)
      : VStmt(Return, Loc), Value(std::move(V)) {}
};

struct VSeqStmt : VStmt {
  std::vector<std::unique_ptr<VStmt>> Stmts;
  VSeqStmt(std::vector<std::unique_ptr<VStmt>> S, SourceLocation Loc)
      : VStmt(Seq, Loc), Stmts(std::move(S)) {}
};

struct VHavocStmt : VStmt {
  std::string Target;
  VHavocStmt(std::string T, SourceLocation Loc)
      : VStmt(Havoc, Loc), Target(std::move(T)) {}
};

struct VWhileStmt : VStmt {
  std::unique_ptr<VExpr> Cond;
  std::vector<std::unique_ptr<VExpr>> Invariants;
  /// Lexicographic termination measure (ordered tuple); empty means none.
  std::vector<std::unique_ptr<VExpr>> Decreases;
  std::vector<std::unique_ptr<VStmt>> Body;
  VWhileStmt(std::unique_ptr<VExpr> C,
             std::vector<std::unique_ptr<VExpr>> Inv,
             std::vector<std::unique_ptr<VExpr>> Dec,
             std::vector<std::unique_ptr<VStmt>> B, SourceLocation Loc)
      : VStmt(While, Loc), Cond(std::move(C)), Invariants(std::move(Inv)),
        Decreases(std::move(Dec)), Body(std::move(B)) {}
};

struct VCallStmt : VStmt {
  /// User-facing source name.
  std::string Callee;
  /// Signature-stable internal identity.
  std::string CalleeIdentity;
  std::vector<std::unique_ptr<VExpr>> Args;
  std::string ResultTarget;
  bool IsProofCall = false;
  VCallStmt(std::string Callee, std::string CalleeIdentity,
            std::vector<std::unique_ptr<VExpr>> Args, std::string ResultTarget,
            SourceLocation Loc, bool IsProofCall = false)
      : VStmt(Call, Loc), Callee(std::move(Callee)),
        CalleeIdentity(std::move(CalleeIdentity)), Args(std::move(Args)),
        ResultTarget(std::move(ResultTarget)), IsProofCall(IsProofCall) {}
};

struct VGhostBlockStmt : VStmt {
  std::vector<std::unique_ptr<VStmt>> Body;
  VGhostBlockStmt(std::vector<std::unique_ptr<VStmt>> B, SourceLocation Loc)
      : VStmt(GhostBlock, Loc), Body(std::move(B)) {}
};

struct VRevealWithFuelStmt : VStmt {
  std::string SpecFunction;
  unsigned Fuel = 1;
  VRevealWithFuelStmt(std::string Fn, unsigned Fuel, SourceLocation Loc)
      : VStmt(RevealWithFuel, Loc), SpecFunction(std::move(Fn)), Fuel(Fuel) {}
};

struct VHideSpecStmt : VStmt {
  std::string SpecFunction;
  VHideSpecStmt(std::string Fn, SourceLocation Loc)
      : VStmt(HideSpec, Loc), SpecFunction(std::move(Fn)) {}
};

struct VRevealSpecStmt : VStmt {
  std::string SpecFunction;
  VRevealSpecStmt(std::string Fn, SourceLocation Loc)
      : VStmt(RevealSpec, Loc), SpecFunction(std::move(Fn)) {}
};

struct VContractAssertStmt : VStmt {
  std::unique_ptr<VExpr> Cond;
  VContractAssertStmt(std::unique_ptr<VExpr> C, SourceLocation Loc)
      : VStmt(ContractAssert, Loc), Cond(std::move(C)) {}
};

std::unique_ptr<VStmt> cloneVStmt(const VStmt *S);

struct VFunction {
  /// User-facing source name.
  std::string Name;
  /// Signature-stable internal identity.
  std::string Identity;
  VType ReturnType;
  VIntMode IntMode = VIntMode::Machine;
  bool IsSpec = false;
  bool IsProof = false;
  bool IsConstexprSpec = false;
  bool RequiresCallDefinedness = false;
  bool IsExternalContract = false;
  bool NeedsDecreasesCheck = false;
  std::map<std::string, unsigned> SpecFuel;
  std::set<std::string> HiddenSpecs;
  std::set<std::string> RevealedSpecs;
  std::vector<std::pair<std::string, VType>> Params;
  std::vector<std::pair<std::string, VType>> ReturnFields;
  std::vector<std::unique_ptr<VExpr>> Preconditions;
  std::vector<std::unique_ptr<VExpr>> Postconditions;
  std::vector<std::unique_ptr<VExpr>> Recommends;
  std::vector<std::unique_ptr<VExpr>> Modifies;
  std::vector<std::pair<std::unique_ptr<VExpr>, std::unique_ptr<VExpr>>> Aliases;
  /// Lexicographic termination measure (ordered tuple); empty means none.
  std::vector<std::unique_ptr<VExpr>> Decreases;
  std::vector<std::unique_ptr<VStmt>> Body;
};

VFunction cloneVFunction(const VFunction &Fn);

} // namespace verify
} // namespace clang

#endif