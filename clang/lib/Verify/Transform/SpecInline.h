//===--- SpecInline.h - Inline spec calls with fuel -----------------------===//
#ifndef LLVM_CLANG_VERIFY_TRANSFORM_SPECINLINE_H
#define LLVM_CLANG_VERIFY_TRANSFORM_SPECINLINE_H

#include "../IR/VStmt.h"
#include "Passivize.h"

namespace clang {
namespace verify {

class SpecInliner {
  const FunctionMap &FnMap;
  std::map<std::string, unsigned> Fuel;

public:
  SpecInliner(const FunctionMap &FnMap, std::map<std::string, unsigned> Fuel)
      : FnMap(FnMap), Fuel(std::move(Fuel)) {}

  void prepareFunction(VFunction &Fn);
  /// Keep VSpecCallExpr for Z3 spec-function applications (no definition inlining).
  void prepareFunctionAxiomatic(VFunction &Fn);
  std::unique_ptr<VExpr> inlineExpr(std::unique_ptr<VExpr> E);

  /// Unfold spec body for defining axiom (fuel-limited symbolic expansion).
  std::unique_ptr<VExpr> unfoldDefinition(const VFunction &Spec,
                                          const std::map<std::string, unsigned> &Fuel,
                                          const std::set<std::string> &Hidden,
                                          const std::set<std::string> &Revealed,
                                          unsigned RootFuel) const;
};

/// Build passive obligations: decreases(callee) < decreases(current) at recursive sites.
PassiveProgram buildDecreasesChecks(const VFunction &Fn, const FunctionMap &FnMap);

bool functionHasRecursiveSpecCall(const VFunction &Fn, const FunctionMap &FnMap);

void collectSpecCalls(const VExpr *E, std::vector<const VSpecCallExpr *> &Out);
void collectSpecCallsInFunction(const VFunction &Fn,
                                std::vector<const VSpecCallExpr *> &Out);

std::unique_ptr<VExpr>
substParamsInExpr(const VExpr *E,
                  const std::map<std::string, std::unique_ptr<VExpr>> &Map);

} // namespace verify
} // namespace clang

#endif