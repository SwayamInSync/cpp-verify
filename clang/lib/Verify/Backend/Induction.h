//===--- Induction.h - Well-founded induction over obligation modules ----===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_INDUCTION_H
#define LLVM_CLANG_VERIFY_BACKEND_INDUCTION_H

#include "Obligation.h"
#include "llvm/Support/Error.h"
#include <map>
#include <optional>
#include <string>
#include <vector>

namespace clang {
namespace verify {

/// The claim at Values of a scheme's variables, for every value of Binders
/// in their ranges where Guard holds.
struct InductionInstance {
  struct Binder {
    std::string Name;
    std::unique_ptr<LogicExpr> Lo;
    std::unique_ptr<LogicExpr> Hi;
  };
  std::vector<Binder> Binders;
  std::unique_ptr<LogicExpr> Guard;
  std::vector<std::unique_ptr<LogicExpr>> Values;
};

/// A well-founded induction over a module. Its claim is the module's
/// obligations other than unwinding ones, without the theorems added to them
/// (ObligationModule::Theorems); the hypothesis is that claim at every value
/// of Variables whose Measure is smaller by the decrease relation of
/// termination checks, all other variables fixed. That relation is
/// well-founded by itself, so the hypothesis holds whatever the measure.
/// Instances are hypotheses at the values a recursive spec's own recursion
/// reaches, ready for the solver; for integer variables the whole hypothesis
/// is given too, as one quantifier.
struct InductionScheme {
  /// For messages: "following fibo", "on n".
  std::string Description;
  /// The recursive spec whose measure and recursion the scheme follows;
  /// empty for an induction on one integer variable.
  std::string Function;
  std::vector<std::pair<std::string, LogicSort>> Variables;
  std::vector<std::unique_ptr<LogicExpr>> Measure;
  std::vector<InductionInstance> Instances;
};

/// The inductions worth trying for \p Module, most specific first: one per
/// recursive spec its claim applies (by that spec's measure at the
/// application), then one per integer variable in an application's
/// arguments.
std::vector<InductionScheme> inductionSchemes(const ObligationModule &Module);

/// \p Module with the hypothesis of \p Scheme assumed by every obligation
/// other than unwinding ones. A proof of it proves the claim everywhere.
llvm::Expected<ObligationModule> inductionModule(const ObligationModule &Module,
                                                 const InductionScheme &Scheme);

/// \p Expr with its free variables in \p Map replaced simultaneously, binders
/// renamed apart from the names of \p Module where a replacement mentions
/// them.
std::unique_ptr<LogicExpr>
substituteFree(const ObligationModule &Module, const LogicExpr *Expr,
               const std::map<std::string, const LogicExpr *> &Map);

/// A deep copy of \p Module; the record of given facts stays shared.
ObligationModule copyObligationModule(const ObligationModule &Module);

/// The time one attempt to settle a module that stayed unresolved may take,
/// all its queries together: an induction that works is found quickly, and a
/// failed one must not cost a whole query budget.
inline unsigned attemptBudgetMs(unsigned TimeoutMs) {
  return TimeoutMs == 0 ? 5000
                        : std::max(TimeoutMs / 6, std::min(TimeoutMs, 2000U));
}

} // namespace verify
} // namespace clang

#endif
