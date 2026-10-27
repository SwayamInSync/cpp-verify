//===--- SubobjectBounds.h - Bounds of subobject pointers -------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_VERIFY_TRANSFORM_SUBOBJECTBOUNDS_H
#define LLVM_CLANG_VERIFY_TRANSFORM_SUBOBJECTBOUNDS_H

#include "../IR/VStmt.h"
#include <optional>
#include <set>
#include <string>

namespace clang {
namespace verify {

/// The companions holding the first byte and the end of the bytes a bounded
/// pointer may address.
std::string lowerBoundName(const std::string &Pointer);
std::string upperBoundName(const std::string &Pointer);
bool isBoundCompanion(const std::string &Name);

/// Whether a pointer value is rooted, through steps, casts, and
/// conditionals, at a pointer in Bounded.
bool hasBoundedRoot(const VExpr *Value, const std::set<std::string> &Bounded);

/// The first byte (or, with Upper, the end) a pointer value may address, as
/// its bounded roots' companions say: through steps and casts, and selected
/// like the value by a conditional. A root that is not bounded may address
/// any byte. Null when the value has no bounded root.
std::unique_ptr<VExpr> pointerBound(const VExpr *Value, bool Upper,
                                    const std::set<std::string> &Bounded);

/// Gives every pointer variable assigned a value rooted at a bounded pointer
/// (Fn.BoundedPointers, which the converter forms with their companions) the
/// value's bounds, and starts every bounded variable that is not a formed
/// subobject pointer with bounds that admit any byte. A step keeps the
/// bounds. Returns the statements that would lose a pointer's bounds:
/// storing it in memory or returning it.
std::vector<std::pair<SourceLocation, std::string>>
propagateSubobjectBounds(VFunction &Fn);

/// Whether a variable is a subobject pointer the converter formed.
bool isFormedSubobjectPointer(const std::string &Name);

/// The prefix of the subobject pointers the converter forms.
extern const char FormedSubobjectPrefix[];

} // namespace verify
} // namespace clang

#endif
