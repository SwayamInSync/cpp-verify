//===--- Passivize.h - Layer 1 to passive SSA IR ----------------*- C++ -*-===//
#ifndef LLVM_CLANG_VERIFY_TRANSFORM_PASSIVIZE_H
#define LLVM_CLANG_VERIFY_TRANSFORM_PASSIVIZE_H

#include "../IR/VStmt.h"
#include <map>
#include <set>

namespace clang {
namespace verify {

using FunctionMap = std::map<std::string, const VFunction *>;

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
  /// Spec registry + per-enclosing-function reveal/hide (for Z3 axiom emission).
  FunctionMap SpecFunctions;
  std::map<std::string, unsigned> SpecFuel;
  std::set<std::string> HiddenSpecs;
  std::set<std::string> RevealedSpecs;
  VIntMode CallerIntMode = VIntMode::Machine;
};

class Passivizer {
  FunctionMap FnMap;

public:
  void setFunctionMap(FunctionMap Map) { FnMap = std::move(Map); }
  PassiveProgram run(const VFunction &Fn);
};

} // namespace verify
} // namespace clang

#endif