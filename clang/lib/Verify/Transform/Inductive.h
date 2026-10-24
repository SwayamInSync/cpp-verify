//===--- Inductive.h - Inductive predicates ---------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_VERIFY_TRANSFORM_INDUCTIVE_H
#define LLVM_CLANG_VERIFY_TRANSFORM_INDUCTIVE_H

#include "../IR/VStmt.h"
#include "llvm/ADT/STLFunctionalExtras.h"
#include <memory>
#include <string>
#include <vector>

namespace clang {
namespace verify {

/// Defines every predicate marked inductive in \p Functions as the least
/// fixpoint of its body, and appends the specs and proof functions that
/// establish its rules. A malformed predicate is reported through \p Report,
/// with the predicate and at its inductive marker, and left as it is.
void expandInductivePredicates(
    std::vector<std::unique_ptr<VFunction>> &Functions,
    llvm::function_ref<void(const VFunction &, SourceLocation, std::string)>
        Report);

} // namespace verify
} // namespace clang

#endif
