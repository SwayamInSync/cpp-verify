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
      R.Reason = VerifyReason::LeanExportFailure;
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
  BMCVerifyBackend(unsigned UnrollBound,
                   const BackendExecutionOptions &Execution)
      : Z3(std::make_unique<Z3VerifyBackend>(Execution, "bmc")),
        UnrollBound(UnrollBound) {}
  llvm::StringRef getName() const override { return "bmc"; }
  BackendCapabilities getCapabilities() const override {
    return {allLogicFeatures(), true};
  }

protected:
  VerifyResult verifyModule(const ObligationModule &Module) override {
    std::vector<VerifyResult> Results = Z3->verifyObligations(Module);
    uint64_t CacheHits = 0;
    uint64_t CacheMisses = 0;
    uint64_t CacheErrors = 0;
    std::string CacheError;
    for (const VerifyResult &Result : Results) {
      CacheHits += Result.CacheHits;
      CacheMisses += Result.CacheMisses;
      CacheErrors += Result.CacheErrors;
      if (CacheError.empty() && !Result.CacheError.empty())
        CacheError = Result.CacheError;
    }
    auto finish = [&](VerifyResult Result) {
      Result.CacheHits = CacheHits;
      Result.CacheMisses = CacheMisses;
      Result.CacheErrors = CacheErrors;
      Result.CacheError = CacheError;
      Result.BackendName = "bmc";
      Result.Bound = UnrollBound;
      return Result;
    };
    std::optional<VerifyResult> FirstUnresolved;
    std::optional<VerifyResult> FailedUnwinding;
    for (VerifyResult Result : std::move(Results)) {
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
        return finish(std::move(Result));
      }
      VerifyResult Unexpected;
      Unexpected.Status = VerifyStatus::Unresolved;
      Unexpected.Reason = VerifyReason::InvalidBackendResult;
      Unexpected.Message = "BMC obligation returned an invalid backend status";
      return finish(std::move(Unexpected));
    }

    if (FirstUnresolved) {
      return finish(std::move(*FirstUnresolved));
    }

    VerifyResult Result;
    if (FailedUnwinding) {
      Result = std::move(*FailedUnwinding);
      Result.Status = VerifyStatus::BoundedSafe;
      Result.Reason = VerifyReason::IncompleteBound;
      Result.Message = "unwinding bound " + std::to_string(UnrollBound) +
                       " is insufficient for a complete proof";
    } else {
      Result.Status = VerifyStatus::Verified;
    }
    return finish(std::move(Result));
  }
};
} // namespace

llvm::StringRef verify::verifyReasonCode(VerifyReason Reason) {
  switch (Reason) {
  case VerifyReason::None:
    return "none";
  case VerifyReason::Counterexample:
    return "counterexample";
  case VerifyReason::SolverTimeout:
    return "solver.timeout";
  case VerifyReason::SolverResourceLimit:
    return "solver.resource-limit";
  case VerifyReason::SolverUnknown:
    return "solver.unknown";
  case VerifyReason::QuerySizeLimit:
    return "query.size-limit";
  case VerifyReason::EncodingFailure:
    return "encoding.failed";
  case VerifyReason::InvalidObligation:
    return "obligation.invalid";
  case VerifyReason::UnsupportedLogic:
    return "logic.unsupported";
  case VerifyReason::MissingQuery:
    return "query.missing";
  case VerifyReason::InvalidBackendResult:
    return "backend.invalid-result";
  case VerifyReason::InconsistentBackendResults:
    return "backend.inconsistent-results";
  case VerifyReason::IncompleteBound:
    return "bmc.incomplete-bound";
  case VerifyReason::LeanExportFailure:
    return "lean.export-failed";
  case VerifyReason::CacheCorrupt:
    return "cache.corrupt";
  case VerifyReason::CacheIOFailure:
    return "cache.io-failed";
  }
  llvm_unreachable("unknown verification reason");
}

VerifyResult VerifyBackend::verify(const ObligationModule &Module) {
  if (!Module.CounterexampleQuery) {
    VerifyResult Result;
    Result.Status = VerifyStatus::Unresolved;
    Result.Reason = VerifyReason::MissingQuery;
    Result.BackendName = getName().str();
    Result.Message = "obligation module has no counterexample query";
    return Result;
  }
  auto ValidatedFeatures = validateObligationModule(Module);
  if (!ValidatedFeatures) {
    VerifyResult Result;
    Result.Status = VerifyStatus::Unresolved;
    Result.Reason = VerifyReason::InvalidObligation;
    Result.BackendName = getName().str();
    Result.Message = "invalid obligation module: " +
                     llvm::toString(ValidatedFeatures.takeError());
    return Result;
  }
  if (*ValidatedFeatures != Module.RequiredFeatures) {
    VerifyResult Result;
    Result.Status = VerifyStatus::Unresolved;
    Result.Reason = VerifyReason::InvalidObligation;
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
    Result.Reason = VerifyReason::UnsupportedLogic;
    Result.BackendName = getName().str();
    Result.Message = "backend '" + getName().str() +
                     "' does not support required logic features: " +
                     formatLogicFeatures(Missing);
    return Result;
  }
  VerifyResult Result = verifyModule(Module);
  if (Result.BackendName.empty())
    Result.BackendName = getName().str();
  if (!Capabilities.ProducesVerificationVerdict &&
      Result.Status != VerifyStatus::Exported &&
      Result.Status != VerifyStatus::Unresolved) {
    Result.Status = VerifyStatus::Unresolved;
    Result.Reason = VerifyReason::InvalidBackendResult;
    Result.Message = "export-only backend '" + getName().str() +
                     "' returned a verification verdict";
    Result.Model.clear();
    Result.Trace.clear();
    Result.ObligationId.clear();
    Result.ObligationType.reset();
    Result.Location = SourceLocation();
    Result.Source = {};
  } else if (Capabilities.ProducesVerificationVerdict &&
             (Result.Status == VerifyStatus::Exported ||
              Result.Status == VerifyStatus::Lowered)) {
    Result.Status = VerifyStatus::Unresolved;
    Result.Reason = VerifyReason::InvalidBackendResult;
    Result.Message = "verifying backend '" + getName().str() +
                     "' returned an export-only result";
    Result.Model.clear();
    Result.Trace.clear();
    Result.ObligationId.clear();
    Result.ObligationType.reset();
    Result.Location = SourceLocation();
    Result.Source = {};
  }
  if (Result.Status == VerifyStatus::Failed &&
      Result.Reason == VerifyReason::None)
    Result.Reason = VerifyReason::Counterexample;
  if (Result.Status == VerifyStatus::Unresolved &&
      Result.Reason == VerifyReason::None)
    Result.Reason = VerifyReason::SolverUnknown;
  if (Result.Status == VerifyStatus::BoundedSafe)
    Result.Reason = VerifyReason::IncompleteBound;
  return Result;
}

std::unique_ptr<VerifyBackend>
verify::createVerifyBackend(BackendKind K, llvm::raw_ostream *LeanOut,
                            unsigned BMCUnroll,
                            const BackendExecutionOptions &Execution,
                            std::vector<std::string> *LeanProjectGoals) {
  switch (K) {
  case BackendKind::Z3:
    return std::make_unique<Z3VerifyBackend>(Execution, "z3");
  case BackendKind::Lean:
    return std::make_unique<LeanVerifyBackend>(LeanOut, LeanProjectGoals);
  case BackendKind::BMC:
    return std::make_unique<BMCVerifyBackend>(BMCUnroll, Execution);
  }
  return std::make_unique<Z3VerifyBackend>(Execution, "z3");
}