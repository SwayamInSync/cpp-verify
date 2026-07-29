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
  ProofObligationKind ProofKind = ProofObligationKind::Assertion;
  std::unique_ptr<VExpr> Cond;
  uint64_t TraceEventCount = 0;
};

enum class PassiveTraceKind {
  Branch,
  Call,
  Loop,
  HeapWrite,
  Allocation,
  LifetimeEnd,
  Deallocation,
  Return
};

struct PassiveTraceValue {
  std::string Label;
  std::unique_ptr<VExpr> Value;
};

struct PassiveTraceEvent {
  PassiveTraceKind Kind = PassiveTraceKind::Branch;
  std::string Message;
  SourceLocation Loc;
  SourceLocation EndLoc;
  std::unique_ptr<VExpr> Guard;
  std::vector<PassiveTraceValue> Values;
};

struct PassiveModelVariable {
  std::string DisplayName;
  VType Type;
  SourceLocation Loc;
  SourceLocation EndLoc;
};

struct PassiveProgram {
  std::string FunctionName;
  std::string FunctionIdentity;
  std::vector<std::unique_ptr<PassiveStmt>> Stmts;
  std::vector<std::unique_ptr<VExpr>> EntryAssumes;
  std::vector<std::unique_ptr<VExpr>> ExitAsserts;
  std::string ResultVarName;
  std::string OldHeapName;
  /// Explicitly declared heap-array SSA variables. Backends must not infer
  /// array sorts from generated variable spellings.
  std::set<std::string> HeapVariables;
  /// Exact source identity for SSA variables eligible for counterexample
  /// presentation. Generated temporaries are deliberately absent.
  std::map<std::string, PassiveModelVariable> ModelVariables;
  std::vector<PassiveTraceEvent> TraceEvents;
  /// Spec registry + per-enclosing-function reveal/hide (for Z3 axiom
  /// emission).
  FunctionMap SpecFunctions;
  std::map<std::string, unsigned> SpecFuel;
  std::set<std::string> HiddenSpecs;
  std::set<std::string> RevealedSpecs;
  VIntMode CallerIntMode = VIntMode::Machine;
};

std::unique_ptr<VExpr> cloneAtEntryState(const VExpr *E);

class Passivizer {
  FunctionMap FnMap;

public:
  void setFunctionMap(FunctionMap Map) { FnMap = std::move(Map); }
  PassiveProgram run(const VFunction &Fn);
};

} // namespace verify
} // namespace clang

#endif