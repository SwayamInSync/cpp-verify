//===--- UBChecks.h - Layer-A undefined-behavior obligations ----*- C++ -*-===//
//
// Instruments a Layer-1 exec/proof function with UB safety obligations (signed
// integer overflow, division/modulo by zero). Each obligation becomes a guarded
// contract_assert that the existing passivize + nested-WP machinery discharges.
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
