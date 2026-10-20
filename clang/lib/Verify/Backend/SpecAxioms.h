//===--- SpecAxioms.h - Verus-style spec SMT axiom generation -------------===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_SPECAXIOMS_H
#define LLVM_CLANG_VERIFY_BACKEND_SPECAXIOMS_H

#include "../Transform/Passivize.h"
#include "Obligation.h"
#include "llvm/Support/Error.h"
#include <set>
#include <vector>

namespace clang {
namespace verify {

struct SpecAxiomContext {
  FunctionMap Functions;
  std::map<std::string, unsigned> SpecFuel;
  std::set<std::string> HiddenSpecs;
  std::set<std::string> RevealedSpecs;
};

/// Collect names of spec functions referenced by VSpecCallExpr in E.
void collectReferencedSpecs(const VExpr *E, std::set<std::string> &Out);

/// Unfold a spec definition for axiom emission (fuel-limited; no call-site
/// args).
std::unique_ptr<VExpr> unfoldSpecDefinition(const VFunction &Spec,
                                            const SpecAxiomContext &Ctx,
                                            unsigned Fuel);

/// Build the one-level body of a recursive spec for its fuel-parameterized
/// defining axiom: the body is expanded a single step and recursive spec calls
/// are kept as uninterpreted applications (the encoder re-attaches the lowered
/// fuel argument to them) rather than fresh constants.
std::unique_ptr<VExpr> unfoldSpecBodyForAxiom(const VFunction &Spec,
                                              const SpecAxiomContext &Ctx);

/// Materialize all logical function declarations and finite definition levels
/// reachable from Module into its owned backend-neutral representation.
/// With \p MaxNodes, the definitions may bring the module from \p Nodes to
/// at most that many nodes (as obligationModuleNodeCount counts them): each
/// is counted as it is lowered, and one past the limit is an
/// ObligationSizeError, or left out when only a counterexample check needs
/// it.
llvm::Error materializeLogicFunctions(ObligationModule &Module,
                                      const SpecAxiomContext &Ctx,
                                      uint64_t MaxNodes = 0,
                                      uint64_t Nodes = 0);

} // namespace verify
} // namespace clang

#endif