//===--- LogicTerms.h - Shared helpers over canonical logic terms --------===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_LOGICTERMS_H
#define LLVM_CLANG_VERIFY_BACKEND_LOGICTERMS_H

#include "Obligation.h"
#include "llvm/ADT/ArrayRef.h"
#include <set>
#include <string>
#include <vector>

namespace clang {
namespace verify {

uint64_t logicNodeCount(const LogicExpr *Expr);
/// The nodes of \p Expr as a tree, each shared subterm counted at each of its
/// places, as a printer that expands terms writes them; once past \p Limit,
/// any count above it.
uint64_t logicTreeNodesUpTo(const LogicExpr *Expr, uint64_t Limit);
/// The distinct nodes of \p Roots, a node they share counted once: what
/// they take in memory.
uint64_t logicDistinctNodes(llvm::ArrayRef<const LogicExpr *> Roots);
bool logicEqual(const LogicExpr *Left, const LogicExpr *Right);
/// A string equal for structurally equal terms.
std::string logicKey(const LogicExpr *Expr);
std::unique_ptr<LogicExpr> logicNot(std::unique_ptr<LogicExpr> Expr);
/// The conjunction of the obligations' goals, as a module's complete goal.
std::unique_ptr<LogicExpr>
logicCompleteGoal(const std::vector<Obligation> &Obligations);
/// Every variable and binder name in \p Expr.
void logicNames(const LogicExpr *Expr, std::set<std::string> &Names);
/// Appends to \p Out, once each and in order of appearance, the variables
/// of \p Expr outside \p Bound and its own binders, with their sorts.
void logicFreeVariables(const LogicExpr *Expr, std::set<std::string> &Bound,
                        std::vector<std::pair<std::string, LogicSort>> &Out);

} // namespace verify
} // namespace clang

#endif
