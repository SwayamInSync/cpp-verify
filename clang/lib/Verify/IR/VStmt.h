//===--- VStmt.h - Layer 1 statements for CppVerify -------------*- C++ -*-===//
#ifndef LLVM_CLANG_VERIFY_IR_VSTMT_H
#define LLVM_CLANG_VERIFY_IR_VSTMT_H

#include "VExpr.h"
#include <memory>
#include <string>
#include <vector>

namespace clang {
namespace verify {

class VStmt {
public:
  enum Kind {
    Assign, Store, If, Assert, Assume, Return, Seq, Havoc
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
  VStoreStmt(std::unique_ptr<VExpr> P, std::unique_ptr<VExpr> V, SourceLocation Loc)
      : VStmt(Store, Loc), Ptr(std::move(P)), Value(std::move(V)) {}
};

struct VIfStmt : VStmt {
  std::unique_ptr<VExpr> Cond;
  std::vector<std::unique_ptr<VStmt>> Then;
  std::vector<std::unique_ptr<VStmt>> Else;
  VIfStmt(std::unique_ptr<VExpr> C, std::vector<std::unique_ptr<VStmt>> T,
          std::vector<std::unique_ptr<VStmt>> E, SourceLocation Loc)
      : VStmt(If, Loc), Cond(std::move(C)), Then(std::move(T)), Else(std::move(E)) {}
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

struct VFunction {
  std::string Name;
  VType ReturnType;
  VIntMode IntMode = VIntMode::Machine;
  std::vector<std::pair<std::string, VType>> Params;
  std::vector<std::unique_ptr<VExpr>> Preconditions;
  std::vector<std::unique_ptr<VExpr>> Postconditions;
  std::vector<std::unique_ptr<VStmt>> Body;
};

} // namespace verify
} // namespace clang

#endif