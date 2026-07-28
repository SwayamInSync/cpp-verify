//===--- Verifier.h -------------------------------------------------------===//
#ifndef LLVM_CLANG_VERIFY_DRIVER_VERIFIER_H
#define LLVM_CLANG_VERIFY_DRIVER_VERIFIER_H

#include "../Backend/VerifyBackend.h"
#include "llvm/Support/raw_ostream.h"
#include <string>

namespace clang {
class ASTContext;

namespace verify {
inline constexpr unsigned DefaultSolverTimeoutMs = 30000;

struct VerifyOptions {
  unsigned DumpIRLayers = 0;
  /// Build and encode verification conditions without invoking a solver.
  bool LowerOnly = false;
  BackendKind Backend = BackendKind::Z3;
  std::string LeanOutPath;
  std::string LeanProjectPath;
  std::string LeanFallbackProjectPath;
  bool LeanCertify = false;
  unsigned BMCUnroll = 10;
  /// Per-query Z3 timeout in milliseconds; 0 disables it. Non-terminating
  /// queries return Unknown instead of hanging the tool.
  unsigned SolverTimeoutMs = DefaultSolverTimeoutMs;
  /// Enable valid(p, n)-based buffer bounds obligations. Core expression
  /// definedness checks are always emitted during passivization.
  bool CheckUB = false;
  /// Optional versioned binary archive for backend-neutral obligation modules.
  llvm::raw_ostream *ObligationOut = nullptr;
};

bool verifyTranslationUnit(ASTContext &Ctx, llvm::raw_ostream &OS,
                           const VerifyOptions &Opts = VerifyOptions());
} // namespace verify
} // namespace clang

#endif