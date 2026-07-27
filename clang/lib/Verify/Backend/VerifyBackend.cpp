//===--- VerifyBackend.cpp ------------------------------------------------===//
#include "VerifyBackend.h"
#include "LeanBackend.h"
#include "Z3Encode.h"

using namespace clang;
using namespace verify;

namespace {
class LeanVerifyBackend : public VerifyBackend {
  llvm::raw_ostream *Out;
  bool PreambleEmitted = false;

public:
  explicit LeanVerifyBackend(llvm::raw_ostream *OS) : Out(OS) {}
  llvm::StringRef getName() const override { return "lean"; }
  BackendCapabilities getCapabilities() const override {
    return {allLogicFeatures(), false};
  }

protected:
  VerifyResult verifyModule(const ObligationModule &Module) override {
    VerifyResult R;
    if (!Out) {
      R.Status = VerifyStatus::Unknown;
      R.Message = "no lean output stream";
      return R;
    }
    VerifyResult Result = exportLeanScratchPad(Module, *Out, !PreambleEmitted);
    PreambleEmitted = true;
    return Result;
  }
};

class BMCVerifyBackend : public VerifyBackend {
  std::unique_ptr<Z3VerifyBackend> Z3;

public:
  explicit BMCVerifyBackend(unsigned TimeoutMs = 0)
      : Z3(std::make_unique<Z3VerifyBackend>(TimeoutMs)) {}
  llvm::StringRef getName() const override { return "bmc"; }
  BackendCapabilities getCapabilities() const override {
    return {allLogicFeatures(), true};
  }

protected:
  VerifyResult verifyModule(const ObligationModule &Module) override {
    return Z3->verify(Module);
  }
};
} // namespace

VerifyResult VerifyBackend::verify(const ObligationModule &Module) {
  const BackendCapabilities Capabilities = getCapabilities();
  const LogicFeatureSet Missing =
      Module.RequiredFeatures & ~Capabilities.SupportedFeatures;
  if (Missing != 0) {
    VerifyResult Result;
    Result.Status = VerifyStatus::Unknown;
    Result.Message = "backend '" + getName().str() +
                     "' does not support required logic features: " +
                     formatLogicFeatures(Missing);
    return Result;
  }
  if (!Module.CounterexampleQuery) {
    VerifyResult Result;
    Result.Status = VerifyStatus::Unknown;
    Result.Message = "obligation module has no counterexample query";
    return Result;
  }
  VerifyResult Result = verifyModule(Module);
  if (!Capabilities.ProducesVerificationVerdict &&
      (Result.Status == VerifyStatus::Verified ||
       Result.Status == VerifyStatus::Failed)) {
    Result.Status = VerifyStatus::Unknown;
    Result.Message = "export-only backend '" + getName().str() +
                     "' returned a verification verdict";
    Result.Model.clear();
    Result.ObligationId.clear();
    Result.Location = SourceLocation();
  } else if (Capabilities.ProducesVerificationVerdict &&
             Result.Status == VerifyStatus::Exported) {
    Result.Status = VerifyStatus::Unknown;
    Result.Message = "verifying backend '" + getName().str() +
                     "' returned an export-only result";
    Result.Model.clear();
    Result.ObligationId.clear();
    Result.Location = SourceLocation();
  }
  return Result;
}

std::unique_ptr<VerifyBackend>
verify::createVerifyBackend(BackendKind K, llvm::raw_ostream *LeanOut,
                            unsigned /*BMCUnroll*/, unsigned SolverTimeoutMs) {
  switch (K) {
  case BackendKind::Z3:
    return std::make_unique<Z3VerifyBackend>(SolverTimeoutMs);
  case BackendKind::Lean:
    return std::make_unique<LeanVerifyBackend>(LeanOut);
  case BackendKind::BMC:
    return std::make_unique<BMCVerifyBackend>(SolverTimeoutMs);
  }
  return std::make_unique<Z3VerifyBackend>(SolverTimeoutMs);
}