//===--- LeanBackend.h - Lean scratch-pad export ------------------------===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_LEANBACKEND_H
#define LLVM_CLANG_VERIFY_BACKEND_LEANBACKEND_H

#include "VerifyBackend.h"
#include "llvm/Support/raw_ostream.h"
#include <set>
#include <vector>

namespace clang {
namespace verify {

VerifyResult exportLeanScratchPad(const ObligationModule &Module,
                                  llvm::raw_ostream &OS, bool EmitPreamble,
                                  std::set<std::string> &EmittedFunctions,
                                  unsigned ModuleIndex,
                                  std::vector<std::string> *ProjectGoals);

} // namespace verify
} // namespace clang

#endif