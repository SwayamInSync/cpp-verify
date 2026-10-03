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
  /// For an unsupported obligation: what the verifier does not model here.
  std::string Note;
  uint64_t TraceEventCount = 0;
  /// The first assumption of a trusted callee's postcondition: the callee,
  /// how many clauses its postcondition has, the call, and the path
  /// condition under which it runs.
  std::string TrustedCallee;
  unsigned PostClauses = 0;
  SourceLocation CallLoc;
  std::unique_ptr<VExpr> CallGuard;
};

/// A goal checked in the final state.
struct PassiveExitAssert {
  ProofObligationKind ProofKind = ProofObligationKind::Postcondition;
  std::unique_ptr<VExpr> Cond;
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
  /// Each behavior's assumption in the entry state.
  std::vector<std::pair<std::string, std::unique_ptr<VExpr>>> BehaviorAssumes;
  std::vector<PassiveExitAssert> ExitAsserts;
  std::string ResultVarName;
  std::string OldHeapName;
  /// Explicitly declared heap-array SSA variables. Backends must not infer
  /// array sorts from generated variable spellings.
  std::set<std::string> HeapVariables;
  /// The specs whose postconditions, and the inductive predicates whose
  /// unfoldings, the program assumes at their applications: what its proof
  /// rests on besides definitions and contracts.
  std::set<std::string> AssumedPosts;
  std::set<std::string> AssumedUnfoldings;
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
  unsigned UnfoldingDepth = 1;
  bool UnfoldingFuel = true;

public:
  void setFunctionMap(FunctionMap Map) { FnMap = std::move(Map); }
  /// How many levels each inductive predicate is unfolded at the
  /// applications a function names, unless reveal_with_fuel asks for more
  /// and \p WithFuel heeds it.
  void setUnfoldingDepth(unsigned Depth, bool WithFuel = true) {
    UnfoldingDepth = Depth;
    UnfoldingFuel = WithFuel;
  }
  PassiveProgram run(const VFunction &Fn);
};

} // namespace verify
} // namespace clang

#endif