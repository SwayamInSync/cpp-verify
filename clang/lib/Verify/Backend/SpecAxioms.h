//===--- SpecAxioms.h - Verus-style spec SMT axiom generation -------------===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_SPECAXIOMS_H
#define LLVM_CLANG_VERIFY_BACKEND_SPECAXIOMS_H

#include "../Transform/Passivize.h"
#include "VCMachine.h"
#include <set>
#include <vector>

namespace clang {
namespace verify {

struct SpecAxiomContext {
  FunctionMap Functions;
  std::map<std::string, unsigned> SpecFuel;
  std::set<std::string> HiddenSpecs;
  std::set<std::string> RevealedSpecs;
  VIntMode CallerIntMode = VIntMode::Machine;
};

/// Collect names of spec functions referenced by VSpecCallExpr in E.
void collectReferencedSpecs(const VExpr *E, std::set<std::string> &Out);

/// Unfold a spec definition for axiom emission (fuel-limited; no call-site args).
std::unique_ptr<VExpr> unfoldSpecDefinition(const VFunction &Spec,
                                            const SpecAxiomContext &Ctx,
                                            unsigned Fuel);

/// Emit defining axioms into Z3 for specs referenced in the VC.
void emitSpecAxioms(class Z3Encoder &Enc, const VCExpr *Goal,
                    const SpecAxiomContext &Ctx);

} // namespace verify
} // namespace clang

#endif