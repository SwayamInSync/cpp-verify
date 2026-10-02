//===--- UBChecks.h - Supplemental UB and bounds obligations ----*- C++ -*-===//
//
// Discovers valid(p, n) extents before spec preparation and instruments a
// Layer-1 exec/proof function with their bounds obligations. Expression
// definedness (overflow, division, shifts, dereferences) is always checked by
// passivization, so it is not repeated here.
//
// See docs/UB-CHECKING.md for the design and the recipe for adding new checks.
//
//===----------------------------------------------------------------------===//
#ifndef LLVM_CLANG_VERIFY_TRANSFORM_UBCHECKS_H
#define LLVM_CLANG_VERIFY_TRANSFORM_UBCHECKS_H

#include "../IR/VStmt.h"
#include <functional>
#include <optional>
#include <set>
#include <string>
#include <vector>

namespace clang {
namespace verify {

/// Insert valid(p, n) bounds obligations into an exec/proof function. No-op
/// for spec functions (the spec world uses unbounded math integers). Returns an
/// error when a recognized marker cannot be interpreted soundly.
std::optional<std::string> instrumentUBChecks(VFunction &Fn);

/// The object a pointer or reference parameter addresses at entry: its
/// declared extent of `Length` elements, or one element when Length is null.
struct AbstractObject {
  std::string Name;
  VType PointerType;
  const VExpr *Length = nullptr;
};

/// The objects of Fn's pointer and reference parameters, after
/// instrumentUBChecks recorded the declared extents.
std::vector<AbstractObject> abstractObjects(const VFunction &Fn);

/// Address lies in one of Objects: [start, end), or [start, end] when Closed.
/// Start and Length are evaluated by Value, which maps a parameter or length
/// expression to the term to use (an entry value).
std::unique_ptr<VExpr> objectMembership(
    const std::vector<AbstractObject> &Objects, const VExpr *Address,
    bool Closed, SourceLocation Loc,
    const std::function<std::unique_ptr<VExpr>(const VExpr *)> &Value);

/// The fact every real object satisfies: it is null or lies at a positive
/// address below the globals.
std::unique_ptr<VExpr> objectPlacement(const AbstractObject &Object,
                                       SourceLocation Loc);

/// The pointer an address steps from: a step or a field offset keeps an
/// address in its base's object.
const VExpr *addressRoot(const VExpr *Addr);

/// The names a statement list assigns, results of calls included.
std::set<std::string>
assignedNames(const std::vector<std::unique_ptr<VStmt>> &Stmts);

/// True when an address is rooted at represented storage, whose own
/// allocation metadata checks its accesses.
bool hasRepresentedRoot(const VExpr *Address);

/// True when the function's contracts mention the `valid(p, n)` extent marker.
/// Without --check-ub the marker's trivial spec body folds to `true` and the
/// declared extent never becomes an assumption, so heap facts do not survive
/// into the postcondition and the solver reports a spurious counterexample.
/// The driver uses this to warn instead of letting that happen silently.
bool usesValidMarker(const VFunction &Fn);

} // namespace verify
} // namespace clang

#endif
