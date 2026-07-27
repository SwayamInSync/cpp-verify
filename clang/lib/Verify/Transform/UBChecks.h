//===--- UBChecks.h - Supplemental UB and bounds obligations ----*- C++ -*-===//
//
// Discovers valid(p, n) extents before spec preparation and instruments a
// Layer-1 exec/proof function with bounds and compatibility safety obligations.
// Core expression definedness is also enforced directly by passivization.
//
// See docs/UB-CHECKING.md for the design and the recipe for adding new checks.
//
//===----------------------------------------------------------------------===//
#ifndef LLVM_CLANG_VERIFY_TRANSFORM_UBCHECKS_H
#define LLVM_CLANG_VERIFY_TRANSFORM_UBCHECKS_H

#include "../IR/VStmt.h"

namespace clang {
namespace verify {

/// Insert UB safety obligations into the body of an exec/proof function. No-op
/// for spec functions (the spec world uses unbounded math integers).
void instrumentUBChecks(VFunction &Fn);

} // namespace verify
} // namespace clang

#endif
