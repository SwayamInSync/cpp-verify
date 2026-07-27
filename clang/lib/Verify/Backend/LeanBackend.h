//===--- LeanBackend.h - Lean scratch-pad export ------------------------===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_LEANBACKEND_H
#define LLVM_CLANG_VERIFY_BACKEND_LEANBACKEND_H

#include "VerifyBackend.h"
#include "llvm/Support/raw_ostream.h"

namespace clang {
namespace verify {

VerifyResult exportLeanScratchPad(const ObligationModule &Module,
                                  llvm::raw_ostream &OS, bool EmitPreamble);

} // namespace verify
} // namespace clang

#endif