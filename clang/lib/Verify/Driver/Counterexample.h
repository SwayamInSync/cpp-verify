//===--- Counterexample.h -------------------------------------------------===//
#ifndef LLVM_CLANG_VERIFY_DRIVER_COUNTEREXAMPLE_H
#define LLVM_CLANG_VERIFY_DRIVER_COUNTEREXAMPLE_H

#include "../Backend/Obligation.h"
#include "../Backend/VerifyBackend.h"
#include <string>

namespace clang {
namespace verify {

/// A counterexample's values by source name, in the order the source
/// declares them, each variable's versions in program order:
/// "a = 100, i = 0 -> 1, result = 151". Empty when it has none.
std::string counterexampleText(const VerifyResult &Result);

/// One step of a counterexample's path, as the static analyzer words its
/// path notes: "takes the false branch", "returns 151".
std::string traceStepText(const VerifyTraceEvent &Event);

/// How many steps of a path are shown: the first and last half of them, as
/// -ftemplate-backtrace-limit shows instantiation contexts.
inline constexpr size_t TraceStepLimit = 10;

/// Where a failed check fails, from its counterexample's values: the part
/// of the check they make false.
struct FailurePlace {
  /// Where the failure is, when that is not the obligation's anchor: the
  /// condition apart from its path condition, its conjunct that is false,
  /// or the call for a callee's clause. In an archive, only its source.
  SourceSpan At;
  ObligationSource AtSource;
  /// For a callee's clause checked at a call: its part that is false, or
  /// the whole clause.
  SourceSpan Clause;
  ObligationSource ClauseSource;
};

/// The place of \p Failure, an obligation of \p Module that failed. The
/// checked condition is found in the obligation's goal, under its chain of
/// assumptions, by where it is written (Obligation::Focus and Clause, or
/// their sources in an archive). A conjunction fails at its first conjunct
/// the values make false (the terms lowering builds for one construct, such
/// as a comparison of a machine and a mathematical value, carry its place);
/// a definedness check, which the verifier builds, also at the check under a
/// short-circuit guard whose left side holds; a disjunction the user writes
/// fails as a whole.
FailurePlace failingPlace(const ObligationModule &Module,
                          const VerifyResult &Failure);

/// The note at the callee's clause of a failure at a call.
std::string clauseNote(const VerifyResult &Failure);

} // namespace verify
} // namespace clang

#endif
