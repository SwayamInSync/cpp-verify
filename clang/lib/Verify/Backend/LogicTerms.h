//===--- LogicTerms.h - Shared helpers over canonical logic terms --------===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_LOGICTERMS_H
#define LLVM_CLANG_VERIFY_BACKEND_LOGICTERMS_H

#include "Obligation.h"
#include <set>
#include <string>
#include <vector>

namespace clang {
namespace verify {

uint64_t logicNodeCount(const LogicExpr *Expr);
bool logicEqual(const LogicExpr *Left, const LogicExpr *Right);
/// A string equal for structurally equal terms.
std::string logicKey(const LogicExpr *Expr);
std::unique_ptr<LogicExpr> logicNot(std::unique_ptr<LogicExpr> Expr);
/// The conjunction of the obligations' goals, as a module's complete goal.
std::unique_ptr<LogicExpr>
logicCompleteGoal(const std::vector<Obligation> &Obligations);
/// Every variable and binder name in \p Expr.
void logicNames(const LogicExpr *Expr, std::set<std::string> &Names);

} // namespace verify
} // namespace clang

#endif
