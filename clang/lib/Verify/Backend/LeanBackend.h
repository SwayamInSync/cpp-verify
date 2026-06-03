//===--- LeanBackend.h - Lean scratch-pad export ------------------------===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_LEANBACKEND_H
#define LLVM_CLANG_VERIFY_BACKEND_LEANBACKEND_H

#include "VerifyBackend.h"
#include "llvm/Support/raw_ostream.h"

namespace clang {
namespace verify {

VerifyResult exportLeanScratchPad(const PassiveProgram &P,
                                  llvm::raw_ostream &OS,
                                  unsigned SolverTimeoutMs = 0);

} // namespace verify
} // namespace clang

#endif