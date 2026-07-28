//===--- Ownership.h - Inferred modular ownership effects -------*- C++ -*-===//
#ifndef LLVM_CLANG_VERIFY_TRANSFORM_OWNERSHIP_H
#define LLVM_CLANG_VERIFY_TRANSFORM_OWNERSHIP_H

#include "../IR/VStmt.h"

namespace clang {
namespace verify {

void inferFreshOwnedReturns(std::vector<std::unique_ptr<VFunction>> &Functions);

} // namespace verify
} // namespace clang

#endif
