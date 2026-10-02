//===--- Origins.h - Objects pointer variables may address ------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_VERIFY_TRANSFORM_ORIGINS_H
#define LLVM_CLANG_VERIFY_TRANSFORM_ORIGINS_H

#include "../IR/VStmt.h"

namespace clang {
namespace verify {

/// Records, on every occurrence of a pointer variable in Fn, the objects it
/// may address there: its origins, as in CompCert's blocks and Frama-C's
/// base addresses. A pointer parameter's origin is its entry object, a
/// global's address its own; pointer arithmetic keeps the origin,
/// assignment copies it, and branches and loops join the possible ones.
/// A pointer loaded from memory or returned by a call has no known origin.
/// A variable that may hold several origins gets the companion
/// `name.__origin`, assigned beside it, and a loop that changes the
/// companion keeps it among the possible origins by a generated invariant.
void annotatePointerOrigins(VFunction &Fn);

/// The origin term of a pointer expression in an annotated function: an
/// identity equal for two pointers exactly when they have one origin. Null
/// when the origin is not known.
std::unique_ptr<VExpr> pointerOriginTerm(const VExpr *E);

/// The identity of one origin.
std::unique_ptr<VExpr> originIdentity(const std::string &Origin,
                                      SourceLocation Loc);

/// The origins a pointer expression may have, or nullopt when unknown.
std::optional<std::vector<std::string>> pointerOrigins(const VExpr *E);

/// Origin names: a parameter's own name, or "@address/size" for a global.
bool isGlobalOrigin(const std::string &Origin);

/// A global origin's address and size in bytes.
std::pair<std::string, uint64_t> globalOriginExtent(const std::string &Origin);

} // namespace verify
} // namespace clang

#endif
