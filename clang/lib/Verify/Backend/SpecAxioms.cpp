//===--- SpecAxioms.cpp - Verus-style spec defining axioms ----------------===//
#include "SpecAxioms.h"
#include "../Transform/SpecInline.h"
#include "Z3Encode.h"

using namespace clang;
using namespace verify;

static void collectReferencedSpecsVC(const VCExpr *E, std::set<std::string> &Out) {
  if (!E)
    return;
  if (E->K == VCExpr::SpecCall)
    Out.insert(E->SpecCallee);
  for (const auto &C : E->Children)
    collectReferencedSpecsVC(C.get(), Out);
}

void verify::collectReferencedSpecs(const VExpr *E, std::set<std::string> &Out) {
  std::vector<const VSpecCallExpr *> Calls;
  collectSpecCalls(E, Calls);
  for (const VSpecCallExpr *C : Calls)
    Out.insert(C->Callee);
}

static unsigned axiomFuelFor(const VFunction &Spec, const SpecAxiomContext &Ctx) {
  if (Ctx.HiddenSpecs.count(Spec.Name))
    return 0;
  if (auto It = Ctx.SpecFuel.find(Spec.Name); It != Ctx.SpecFuel.end())
    return It->second;
  if (Ctx.RevealedSpecs.count(Spec.Name))
    return 1;
  if (!Spec.NeedsDecreasesCheck)
    return 64;
  return 0;
}

std::unique_ptr<VExpr> verify::unfoldSpecDefinition(const VFunction &Spec,
                                                    const SpecAxiomContext &Ctx,
                                                    unsigned Fuel) {
  SpecInliner Inliner(Ctx.Functions, Ctx.SpecFuel);
  return Inliner.unfoldDefinition(Spec, Ctx.SpecFuel, Ctx.HiddenSpecs,
                                  Ctx.RevealedSpecs, Fuel);
}

std::unique_ptr<VExpr> verify::unfoldSpecBodyForAxiom(const VFunction &Spec,
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
  std::set<std::string> Used;
  collectReferencedSpecsVC(Goal, Used);
  for (const auto &Name : Used)
    Enc.emitSpecDefiningAxiom(Name, Ctx);
}