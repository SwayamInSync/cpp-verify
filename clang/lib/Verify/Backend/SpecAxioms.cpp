//===--- SpecAxioms.cpp - Verus-style spec defining axioms ----------------===//
#include "SpecAxioms.h"
#include "../Transform/SpecInline.h"
#include "Z3Encode.h"

using namespace clang;
using namespace verify;

static void collectSpecCallsVC(const VCExpr *E,
                               std::vector<const VCExpr *> &Out) {
  if (!E)
    return;
  if (E->K == VCExpr::SpecCall)
    Out.push_back(E);
  for (const auto &C : E->Children)
    collectSpecCallsVC(C.get(), Out);
}

void verify::collectReferencedSpecs(const VExpr *E,
                                    std::set<std::string> &Out) {
  std::vector<const VSpecCallExpr *> Calls;
  collectSpecCalls(E, Calls);
  for (const VSpecCallExpr *C : Calls)
    Out.insert(C->CalleeIdentity);
}

std::unique_ptr<VExpr> verify::unfoldSpecDefinition(const VFunction &Spec,
                                                    const SpecAxiomContext &Ctx,
                                                    unsigned Fuel) {
  SpecInliner Inliner(Ctx.Functions, Ctx.SpecFuel);
  return Inliner.unfoldDefinition(Spec, Ctx.SpecFuel, Ctx.HiddenSpecs,
                                  Ctx.RevealedSpecs, Fuel);
}

std::unique_ptr<VExpr>
verify::unfoldSpecBodyForAxiom(const VFunction &Spec,
                               const SpecAxiomContext &Ctx) {
  // One step of unfolding (RootFuel = 1) with recursive leaves kept as spec
  // applications. Hidden/revealed sets are intentionally empty so the body is
  // expanded one level regardless of the caller's reveal state.
  SpecInliner Inliner(Ctx.Functions, Ctx.SpecFuel);
  return Inliner.unfoldDefinition(Spec, {}, {}, {}, /*RootFuel=*/1,
                                  /*KeepLeaves=*/true);
}

void verify::emitSpecAxioms(Z3Encoder &Enc, const VCExpr *Goal,
                            const SpecAxiomContext &Ctx) {
  std::vector<const VCExpr *> Calls;
  collectSpecCallsVC(Goal, Calls);
  for (const VCExpr *Call : Calls)
    Enc.emitSpecCallAxiom(Call, Ctx);
}