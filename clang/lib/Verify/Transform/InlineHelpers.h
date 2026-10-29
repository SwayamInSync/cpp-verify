//===--- InlineHelpers.h - Calls of functions without contracts -*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_VERIFY_TRANSFORM_INLINEHELPERS_H
#define LLVM_CLANG_VERIFY_TRANSFORM_INLINEHELPERS_H

#include "../IR/VStmt.h"
#include <map>
#include <memory>
#include <string>
#include <vector>

namespace clang {
namespace verify {

/// The most statements the calls of one function may inline.
inline constexpr size_t MaxInlinedStatements = 2000;

/// Replaces every call of a function without a contract
/// (VCallStmt::InlinesHelper) with the callee's body as converted, renamed
/// apart: its parameters are locals initialized from the arguments, and each
/// return assigns the call's result and sets a flag that skips the rest of
/// the body (a break inside a loop, whose generated invariant says the flag
/// is clear). Calls in the inlined bodies are inlined in turn. A call that
/// cannot be inlined (recursion, the size budget, a construct the inlining
/// does not support) becomes an unsupported obligation that says why. A
/// function without a contract is verified where it is inlined, so those
/// some call inlines are removed, with those converted only to be inlined
/// (VFunction::IsInlineHelper).
/// \p Unconverted names, by identity, the helpers whose bodies could not be
/// converted, with why; a call of one says so.
void inlineHelperCalls(
    std::vector<std::unique_ptr<VFunction>> &Functions,
    const std::map<std::string, std::string> &Unconverted = {});

} // namespace verify
} // namespace clang

#endif
