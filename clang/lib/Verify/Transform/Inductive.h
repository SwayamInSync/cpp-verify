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
#include <memory>
#include <string>
#include <vector>

namespace clang {
namespace verify {

/// Defines every predicate marked inductive in \p Functions as the least
/// fixpoint of its body, and appends the specs and proof functions that
/// establish its rules. A malformed predicate is reported in \p Errors and
/// left as it is.
void expandInductivePredicates(
    std::vector<std::unique_ptr<VFunction>> &Functions,
    std::vector<std::string> &Errors);

} // namespace verify
} // namespace clang

#endif
