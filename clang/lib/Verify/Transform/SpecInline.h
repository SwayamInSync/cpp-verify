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
  /// When KeepLeaves is set, recursive spec calls that are not unfolded further
  /// are kept as uninterpreted applications of the same spec function (used to
  /// build a recursive spec's one-level fuel-parameterized defining axiom)
  /// instead of being replaced by fresh constants.
  std::unique_ptr<VExpr> unfoldDefinition(const VFunction &Spec,
                                          const std::map<std::string, unsigned> &Fuel,
                                          const std::set<std::string> &Hidden,
                                          const std::set<std::string> &Revealed,
                                          unsigned RootFuel,
                                          bool KeepLeaves = false) const;
};

/// Build passive obligations: decreases(callee) < decreases(current) at recursive sites.
PassiveProgram buildDecreasesChecks(const VFunction &Fn, const FunctionMap &FnMap);

bool functionHasRecursiveSpecCall(const VFunction &Fn, const FunctionMap &FnMap);

/// The key substParamsInExpr maps `result` under.
inline constexpr const char *ResultKey = "<result>";

/// The conjunction of \p Spec's postconditions at \p Args, with \p Value as
/// its result and its own heap reads in \p Heap; null when it has none.
std::unique_ptr<VExpr> specPostcondition(
    const VFunction &Spec, const std::vector<std::unique_ptr<VExpr>> &Args,
    const VExpr *Value, SourceLocation Loc, const std::string &Heap = {});

/// What holds at an application of \p Spec: its postconditions and, for an
/// inductive predicate, its unfolding; null when nothing does.
std::unique_ptr<VExpr> specApplicationFacts(
    const VFunction &Spec, const std::vector<std::unique_ptr<VExpr>> &Args,
    const VExpr *Value, SourceLocation Loc, const std::string &Heap = {});

/// Build passive obligations for a non-recursive spec: its postconditions
/// hold of its body, assuming those of the specs it calls.
PassiveProgram buildSpecPostChecks(const VFunction &Fn,
                                   const FunctionMap &FnMap);

/// Build passive obligations: every load of a spec with a reads clause, and
/// every range a heap-reading callee reads, lies within its reads ranges.
/// \p Missing names a heap-reading callee without a reads clause.
PassiveProgram buildReadsChecks(const VFunction &Fn, const FunctionMap &FnMap,
                                std::string &Missing);

/// The address lies outside every reads range of \p Spec at \p Args.
std::unique_ptr<VExpr>
addressOutsideReads(const VFunction &Spec,
                    const std::vector<std::unique_ptr<VExpr>> &Args,
                    const VExpr *Address, SourceLocation Loc);

/// The byte range [Lo, Hi) is disjoint from every reads range of \p Spec at
/// \p Args.
std::unique_ptr<VExpr>
regionOutsideReads(const VFunction &Spec,
                   const std::vector<std::unique_ptr<VExpr>> &Args,
                   const VExpr *Lo, const VExpr *Hi, SourceLocation Loc);

void collectSpecCalls(const VExpr *E, std::vector<const VSpecCallExpr *> &Out);
void collectSpecCallsInFunction(const VFunction &Fn,
                                std::vector<const VSpecCallExpr *> &Out);

std::unique_ptr<VExpr>
substParamsInExpr(const VExpr *E,
                  const std::map<std::string, std::unique_ptr<VExpr>> &Map);

} // namespace verify
} // namespace clang

#endif