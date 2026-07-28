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
  std::set<std::string> EmittedFunctions;
  std::set<std::string> EmittedTheorems;
  unsigned ModuleIndex = 0;
  std::vector<std::string> *ProjectGoals;

public:
  LeanVerifyBackend(llvm::raw_ostream *OS,
                    std::vector<std::string> *ProjectGoals)
      : Out(OS), ProjectGoals(ProjectGoals) {}
  llvm::StringRef getName() const override { return "lean"; }
  BackendCapabilities getCapabilities() const override {
    return {allLogicFeatures(), false};
  }

protected:
  VerifyResult verifyModule(const ObligationModule &Module) override {
    VerifyResult R;
    if (!Out) {
      R.Status = VerifyStatus::Unresolved;
      R.Message = "no lean output stream";
      return R;
    }
    VerifyResult Result =
        exportLeanScratchPad(Module, *Out, !PreambleEmitted, EmittedFunctions,
                             EmittedTheorems, ++ModuleIndex, ProjectGoals);
    PreambleEmitted = true;
    return Result;
  }
};

class BMCVerifyBackend : public VerifyBackend {
  std::unique_ptr<Z3VerifyBackend> Z3;
  unsigned UnrollBound;

public:
  BMCVerifyBackend(unsigned UnrollBound, unsigned TimeoutMs = 0)
      : Z3(std::make_unique<Z3VerifyBackend>(TimeoutMs)),
        UnrollBound(UnrollBound) {}
  llvm::StringRef getName() const override { return "bmc"; }
  BackendCapabilities getCapabilities() const override {
    return {allLogicFeatures(), true};
  }

protected:
  VerifyResult verifyModule(const ObligationModule &Module) override {
    std::optional<VerifyResult> FirstUnresolved;
    std::optional<VerifyResult> FailedUnwinding;
    for (VerifyResult Result : Z3->verifyObligations(Module)) {
      if (Result.Status == VerifyStatus::Verified)
        continue;
      if (Result.Status == VerifyStatus::Unresolved) {
        if (!FirstUnresolved)
          FirstUnresolved = std::move(Result);
        continue;
      }
      if (Result.Status == VerifyStatus::Failed &&
          Result.ObligationType == ObligationKind::Unwinding) {
        if (!FailedUnwinding)
          FailedUnwinding = std::move(Result);
        continue;
      }
      if (Result.Status == VerifyStatus::Failed) {
        Result.BackendName = "bmc";
        Result.Bound = UnrollBound;
        return Result;
      }
      VerifyResult Unexpected;
      Unexpected.Status = VerifyStatus::Unresolved;
      Unexpected.Message = "BMC obligation returned an invalid backend status";
      Unexpected.BackendName = "bmc";
      Unexpected.Bound = UnrollBound;
      return Unexpected;
    }

    if (FirstUnresolved) {
      FirstUnresolved->BackendName = "bmc";
      FirstUnresolved->Bound = UnrollBound;
      return std::move(*FirstUnresolved);
    }

    VerifyResult Result;
    if (FailedUnwinding) {
      Result = std::move(*FailedUnwinding);
      Result.Status = VerifyStatus::BoundedSafe;
      Result.Message = "unwinding bound " + std::to_string(UnrollBound) +
                       " is insufficient for a complete proof";
    } else {
      Result.Status = VerifyStatus::Verified;
    }
    Result.BackendName = "bmc";
    Result.Bound = UnrollBound;
    return Result;
  }
};
} // namespace

VerifyResult VerifyBackend::verify(const ObligationModule &Module) {
  auto ValidatedFeatures = validateObligationModule(Module);
  if (!ValidatedFeatures) {
    VerifyResult Result;
    Result.Status = VerifyStatus::Unresolved;
    Result.BackendName = getName().str();
    Result.Message = "invalid obligation module: " +
                     llvm::toString(ValidatedFeatures.takeError());
    return Result;
  }
  if (*ValidatedFeatures != Module.RequiredFeatures) {
    VerifyResult Result;
    Result.Status = VerifyStatus::Unresolved;
    Result.BackendName = getName().str();
    Result.Message =
        "obligation feature declaration does not match validated contents";
    return Result;
  }
  const BackendCapabilities Capabilities = getCapabilities();
  const LogicFeatureSet Missing =
      Module.RequiredFeatures & ~Capabilities.SupportedFeatures;
  if (Missing != 0) {
    VerifyResult Result;
    Result.Status = VerifyStatus::Unresolved;
    Result.BackendName = getName().str();
    Result.Message = "backend '" + getName().str() +
                     "' does not support required logic features: " +
                     formatLogicFeatures(Missing);
    return Result;
  }
  if (!Module.CounterexampleQuery) {
    VerifyResult Result;
    Result.Status = VerifyStatus::Unresolved;
    Result.BackendName = getName().str();
    Result.Message = "obligation module has no counterexample query";
    return Result;
  }
  VerifyResult Result = verifyModule(Module);
  if (Result.BackendName.empty())
    Result.BackendName = getName().str();
  if (!Capabilities.ProducesVerificationVerdict &&
      Result.Status != VerifyStatus::Exported &&
      Result.Status != VerifyStatus::Unresolved) {
    Result.Status = VerifyStatus::Unresolved;
    Result.Message = "export-only backend '" + getName().str() +
                     "' returned a verification verdict";
    Result.Model.clear();
    Result.ObligationId.clear();
    Result.ObligationType.reset();
    Result.Location = SourceLocation();
  } else if (Capabilities.ProducesVerificationVerdict &&
             (Result.Status == VerifyStatus::Exported ||
              Result.Status == VerifyStatus::Lowered)) {
    Result.Status = VerifyStatus::Unresolved;
    Result.Message = "verifying backend '" + getName().str() +
                     "' returned an export-only result";
    Result.Model.clear();
    Result.ObligationId.clear();
    Result.ObligationType.reset();
    Result.Location = SourceLocation();
  }
  return Result;
}

std::unique_ptr<VerifyBackend>
verify::createVerifyBackend(BackendKind K, llvm::raw_ostream *LeanOut,
                            unsigned BMCUnroll, unsigned SolverTimeoutMs,
                            std::vector<std::string> *LeanProjectGoals) {
  switch (K) {
  case BackendKind::Z3:
    return std::make_unique<Z3VerifyBackend>(SolverTimeoutMs);
  case BackendKind::Lean:
    return std::make_unique<LeanVerifyBackend>(LeanOut, LeanProjectGoals);
  case BackendKind::BMC:
    return std::make_unique<BMCVerifyBackend>(BMCUnroll, SolverTimeoutMs);
  }
  return std::make_unique<Z3VerifyBackend>(SolverTimeoutMs);
}

VerifyResult verify::lowerObligationModule(const ObligationModule &Module,
                                           llvm::raw_ostream *Z3Out,
                                           unsigned SolverTimeoutMs) {
  Z3Encoder Encoder;
  Encoder.setTimeoutMs(SolverTimeoutMs);
  return Encoder.lowerModule(Module, Z3Out);
}