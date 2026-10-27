//===--- OutParameters.h - Parameters written before read -------*- C++ -*-===//
//
// Finds the pointer and reference parameters whose storage a verified body
// never reads before writing it, so that a caller may pass storage that is
// not initialized ([dcl.init.ref], [basic.indet]): binding a reference or
// passing a pointer reads nothing.
//
//===----------------------------------------------------------------------===//
#ifndef LLVM_CLANG_VERIFY_TRANSFORM_OUTPARAMETERS_H
#define LLVM_CLANG_VERIFY_TRANSFORM_OUTPARAMETERS_H

#include "../IR/VStmt.h"

namespace clang {
namespace verify {

/// Sets VFunction::OutParameters of every function with a verified body, and
/// removes from their generated validity preconditions the initialization
/// they no longer require, and from their bodies the initialization a
/// reference bound to part of one assumed of its object.
void inferOutParameters(std::vector<std::unique_ptr<VFunction>> &Functions);

} // namespace verify
} // namespace clang

#endif
