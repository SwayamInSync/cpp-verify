//===--- Verifier.h -------------------------------------------------------===//
#ifndef LLVM_CLANG_VERIFY_DRIVER_VERIFIER_H
#define LLVM_CLANG_VERIFY_DRIVER_VERIFIER_H

#include "llvm/Support/raw_ostream.h"

namespace clang {
class ASTContext;

namespace verify {
struct VerifyOptions {
  /// Bitmask of IRLayer values; 0 disables IR dumps.
  unsigned DumpIRLayers = 0;
};

bool verifyTranslationUnit(ASTContext &Ctx, llvm::raw_ostream &OS,
                           const VerifyOptions &Opts = VerifyOptions());
} // namespace verify
} // namespace clang

#endif