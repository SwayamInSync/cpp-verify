//===--- VHash.h - Semantic digests of Layer 1 functions --------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
#ifndef LLVM_CLANG_VERIFY_IR_VHASH_H
#define LLVM_CLANG_VERIFY_IR_VHASH_H

#include "VStmt.h"
#include "llvm/ADT/STLFunctionalExtras.h"
#include <set>
#include <string>

namespace clang {
namespace verify {

/// Bumped whenever the serialization a digest is taken of changes.
inline constexpr unsigned VFunctionDigestVersion = 1;

/// What of a function a digest covers.
enum class VDigestScope {
  /// Everything.
  Whole,
  /// Everything but the body and the bodies of the clause proofs: what a
  /// caller of an executable or proof function may rely on.
  Interface
};

struct VFunctionDigest {
  /// SHA-256, in hexadecimal, of the function without its source positions:
  /// two functions with one digest are verified alike. Whether a position
  /// is present is covered, since the verifier branches on that.
  std::string Hash;
  /// Every identity the covered part names: callees, specs applied,
  /// revealed or hidden, and the groups the function belongs to.
  std::set<std::string> References;
};

/// With \p Place, the digest also covers where everything is: what
/// \p Place gives for each position that is there.
VFunctionDigest
digestVFunction(const VFunction &Fn, VDigestScope Scope = VDigestScope::Whole,
                llvm::function_ref<std::string(SourceLocation)> Place = nullptr);

} // namespace verify
} // namespace clang

#endif
