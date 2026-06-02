//===--- Verifier.h -------------------------------------------------------===//
#ifndef LLVM_CLANG_VERIFY_DRIVER_VERIFIER_H
#define LLVM_CLANG_VERIFY_DRIVER_VERIFIER_H

#include "../Backend/VerifyBackend.h"
#include "llvm/Support/raw_ostream.h"
#include <string>

namespace clang {
class ASTContext;

namespace verify {
struct VerifyOptions {
  unsigned DumpIRLayers = 0;
  BackendKind Backend = BackendKind::Z3;
  std::string LeanOutPath;
  unsigned BMCUnroll = 10;
};

bool verifyTranslationUnit(ASTContext &Ctx, llvm::raw_ostream &OS,
                           const VerifyOptions &Opts = VerifyOptions());
} // namespace verify
} // namespace clang

#endif