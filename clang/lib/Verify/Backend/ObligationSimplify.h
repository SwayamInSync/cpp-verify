//===--- ObligationSimplify.h - Canonical obligation simplification -*- C++
//-*-===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_OBLIGATIONSIMPLIFY_H
#define LLVM_CLANG_VERIFY_BACKEND_OBLIGATIONSIMPLIFY_H

#include "Obligation.h"

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

} // namespace verify
} // namespace clang

#endif
