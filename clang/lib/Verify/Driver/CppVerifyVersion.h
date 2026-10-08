//===--- CppVerifyVersion.h - cpp-verify and backend versions -------------===//
#ifndef LLVM_CLANG_VERIFY_DRIVER_CPPVERIFYVERSION_H
#define LLVM_CLANG_VERIFY_DRIVER_CPPVERIFYVERSION_H

#include "llvm/ADT/StringRef.h"
#include "llvm/Support/raw_ostream.h"

namespace clang {
namespace verify {

/// The Lean toolchain every generated Lean project pins.
inline constexpr llvm::StringLiteral LeanToolchain = "leanprover/lean4:v4.32.2";

/// The cvc5 release the test suite runs with.
inline constexpr llvm::StringLiteral CVC5TestedVersion = "1.1.2";

/// Prints cpp-verify's version, the LLVM release it is built on, and each
/// verification backend: the linked Z3, and the cvc5 and Lean programs a
/// verification run would find on PATH.
void printVersion(llvm::raw_ostream &OS);

} // namespace verify
} // namespace clang

#endif
