//===--- Passivize.h - Layer 1 to passive SSA IR ----------------*- C++ -*-===//
#ifndef LLVM_CLANG_VERIFY_TRANSFORM_PASSIVIZE_H
#define LLVM_CLANG_VERIFY_TRANSFORM_PASSIVIZE_H

#include "../IR/VStmt.h"

namespace clang {
namespace verify {

struct PassiveStmt {
  enum Kind { Assume, Assert };
  Kind K = Assume;
  std::unique_ptr<VExpr> Cond;
};

struct PassiveProgram {
  std::vector<std::unique_ptr<PassiveStmt>> Stmts;
  std::vector<std::unique_ptr<VExpr>> EntryAssumes;
  std::vector<std::unique_ptr<VExpr>> ExitAsserts;
  std::string ResultVarName;
  std::string OldHeapName;
};

class Passivizer {
public:
  PassiveProgram run(const VFunction &Fn);
};

} // namespace verify
} // namespace clang

#endif