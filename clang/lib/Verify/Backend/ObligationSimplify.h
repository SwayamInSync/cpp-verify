//===--- ObligationSimplify.h - Canonical obligation simplification -*- C++
//-*-===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_OBLIGATIONSIMPLIFY_H
#define LLVM_CLANG_VERIFY_BACKEND_OBLIGATIONSIMPLIFY_H

#include "Obligation.h"
#include <algorithm>
#include <utility>
#include <vector>

namespace clang {
namespace verify {

struct ObligationSimplificationStats {
  uint64_t NodesBefore = 0;
  uint64_t NodesAfter = 0;
  uint64_t Rewrites = 0;
  uint64_t FunctionsRemoved = 0;
};

/// Count canonical expression nodes across goals, queries, and reachable
/// logical declarations. Diagnostic-only metadata is excluded.
uint64_t obligationModuleNodeCount(const ObligationModule &Module);

/// Apply conservative, semantics-preserving canonical rewrites and remove
/// logical declarations unreachable from any proof obligation. The returned
/// module is fully revalidated with exact goal/query invariants rebuilt.
llvm::Expected<ObligationModule>
simplifyObligationModule(ObligationModule Module,
                         ObligationSimplificationStats *Stats = nullptr);

/// \p Query with each quantifier joined by its instances at the closed
/// memory reads of the query that read where its body reads: a body read at
/// Base + S * k and a closed read at Base + S * t give the instance at t.
/// Null when there is none. forall k. B is forall k. B && B(t), and
/// exists k. B is exists k. B || B(t), so the meaning is unchanged; they
/// supply what pattern matching misses once a solver folds a ground address
/// such as p + 2 * 4 to p + 8.
std::unique_ptr<LogicExpr> instantiateAtReads(const LogicExpr &Query);

/// \p Query with each closed sequence equality it refutes (an a == b where
/// the query asserts its negation, or an asserted a != b) joined by
/// extensionality: a == b || (len(a) == len(b) && forall k in [0, len(a)).
/// a[k] == b[k]). Null when there is none. Both sides are equivalent, so the
/// meaning is unchanged; they let a solver prove an equality from equal
/// elements, which a native sequence theory rarely does by itself.
std::unique_ptr<LogicExpr> instantiateExtensionality(const LogicExpr &Query);

} // namespace verify
} // namespace clang

#endif
