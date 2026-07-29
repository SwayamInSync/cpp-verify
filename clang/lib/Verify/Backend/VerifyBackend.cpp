//===--- VerifyBackend.cpp ------------------------------------------------===//
#include "VerifyBackend.h"
#include "CVC5Backend.h"
#include "LeanBackend.h"
#include "ObligationSimplify.h"
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
  unsigned MaxUnrollBound;

public:
  BMCVerifyBackend(unsigned UnrollBound,
                   const BackendExecutionOptions &Execution)
      : Z3(std::make_unique<Z3VerifyBackend>(Execution, "bmc",
                                             /*ReuseVerifiedQueries=*/true)),
        MaxUnrollBound(UnrollBound) {}
  llvm::StringRef getName() const override { return "bmc"; }
  BackendCapabilities getCapabilities() const override {
    return {allLogicFeatures(), true};
  }

protected:
  VerifyResult verifyModule(const ObligationModule &Module) override {
    if (!Module.BMCTransform) {
      VerifyResult Result;
      Result.Status = VerifyStatus::Unresolved;
      Result.Reason = VerifyReason::InvalidBackendResult;
      Result.Message = "BMC backend requires bounded transform provenance";
      return Result;
    }
    const unsigned UnrollBound = Module.BMCTransform->UnrollBound;
    if (UnrollBound > MaxUnrollBound) {
      VerifyResult Result;
      Result.Status = VerifyStatus::Unresolved;
      Result.Reason = VerifyReason::InvalidBackendResult;
      Result.Message = "BMC module bound exceeds the configured maximum";
      Result.Bound = UnrollBound;
      return Result;
    }
    std::vector<VerifyResult> Results = Z3->verifyObligations(Module);
    uint64_t CacheHits = 0;
    uint64_t CacheMisses = 0;
    uint64_t CacheErrors = 0;
    uint64_t ReusedQueries = 0;
    std::string CacheError;
    for (const VerifyResult &Result : Results) {
      CacheHits += Result.CacheHits;
      CacheMisses += Result.CacheMisses;
      CacheErrors += Result.CacheErrors;
      ReusedQueries += Result.ReusedQueries;
      if (CacheError.empty() && !Result.CacheError.empty())
        CacheError = Result.CacheError;
    }
    auto finish = [&](VerifyResult Result) {
      Result.CacheHits = CacheHits;
      Result.CacheMisses = CacheMisses;
      Result.CacheErrors = CacheErrors;
      Result.CacheError = CacheError;
      Result.ReusedQueries = ReusedQueries;
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

class PortfolioVerifyBackend : public VerifyBackend {
  std::unique_ptr<Z3VerifyBackend> Z3;
  std::unique_ptr<CVC5VerifyBackend> CVC5;
  uint64_t MaxQueryNodes;

  static llvm::StringRef statusName(VerifyStatus Status) {
    switch (Status) {
    case VerifyStatus::Verified:
      return "verified";
    case VerifyStatus::Failed:
      return "failed";
    case VerifyStatus::Unresolved:
      return "unresolved";
    case VerifyStatus::Lowered:
      return "lowered";
    case VerifyStatus::BoundedSafe:
      return "bounded-safe";
    case VerifyStatus::Exported:
      return "exported";
    case VerifyStatus::Certified:
      return "certified";
    }
    return "invalid";
  }

  static VerifyResult unresolvedPair(VerifyResult Z3Result,
                                     VerifyResult CVC5Result,
                                     bool IsDisagreement) {
    VerifyResult Result;
    Result.Status = VerifyStatus::Unresolved;
    Result.Reason =
        IsDisagreement
            ? VerifyReason::InconsistentBackendResults
            : (Z3Result.Status == VerifyStatus::Unresolved ? Z3Result.Reason
                                                           : CVC5Result.Reason);
    if (Result.Reason == VerifyReason::None)
      Result.Reason = VerifyReason::SolverUnknown;
    Result.Message = std::string(IsDisagreement ? "backend disagreement"
                                                : "incomplete portfolio") +
                     ": z3=" + statusName(Z3Result.Status).str() +
                     ", cvc5=" + statusName(CVC5Result.Status).str();
    const VerifyResult &Detail =
        Z3Result.Status == VerifyStatus::Unresolved ? Z3Result : CVC5Result;
    if (!Detail.Message.empty())
      Result.Message += " (" + Detail.Message + ")";
    Result.ObligationId = !Z3Result.ObligationId.empty()
                              ? std::move(Z3Result.ObligationId)
                              : std::move(CVC5Result.ObligationId);
    Result.ObligationType = Z3Result.ObligationType ? Z3Result.ObligationType
                                                    : CVC5Result.ObligationType;
    Result.Location =
        Z3Result.Location.isValid() ? Z3Result.Location : CVC5Result.Location;
    Result.Source = Z3Result.Source.isValid() ? std::move(Z3Result.Source)
                                              : std::move(CVC5Result.Source);
    return Result;
  }

  static bool isDecisive(VerifyStatus Status) {
    return Status == VerifyStatus::Verified || Status == VerifyStatus::Failed;
  }

public:
  explicit PortfolioVerifyBackend(const BackendExecutionOptions &Execution)
      : Z3(std::make_unique<Z3VerifyBackend>(Execution,
                                             "portfolio-z3-component")),
        CVC5(std::make_unique<CVC5VerifyBackend>(Execution)),
        MaxQueryNodes(Execution.MaxQueryNodes) {}

  llvm::StringRef getName() const override { return "portfolio"; }
  BackendCapabilities getCapabilities() const override {
    return {Z3->getCapabilities().SupportedFeatures &
                CVC5->getCapabilities().SupportedFeatures,
            true};
  }

protected:
  VerifyResult verifyModule(const ObligationModule &Module) override {
    if (MaxQueryNodes != 0 &&
        obligationModuleNodeCount(Module) > MaxQueryNodes) {
      VerifyResult Result;
      Result.Status = VerifyStatus::Unresolved;
      Result.Reason = VerifyReason::QuerySizeLimit;
      Result.Message =
          "canonical obligation module exceeds query node budget " +
          std::to_string(MaxQueryNodes);
      Result.BackendName = "portfolio";
      return Result;
    }

    std::vector<VerifyResult> Z3Results;
    std::vector<VerifyResult> CVC5Results;
    if (Module.Obligations.empty()) {
      Z3Results.push_back(Z3->verify(Module));
      CVC5Results.push_back(CVC5->verify(Module));
    } else {
      Z3Results = Z3->verifyObligations(Module);
      CVC5Results = CVC5->verifyObligations(Module);
    }
    if (Z3Results.size() != CVC5Results.size()) {
      VerifyResult Result;
      Result.Status = VerifyStatus::Unresolved;
      Result.Reason = VerifyReason::InvalidBackendResult;
      Result.Message = "portfolio adapters returned different result counts";
      Result.BackendName = "portfolio";
      return Result;
    }

    uint64_t CacheHits = 0;
    uint64_t CacheMisses = 0;
    uint64_t CacheErrors = 0;
    uint64_t ReusedQueries = 0;
    std::string CacheError;
    std::optional<VerifyResult> FirstDisagreement;
    std::optional<VerifyResult> FirstFailure;
    std::optional<VerifyResult> FirstUnresolved;
    for (size_t I = 0; I != Z3Results.size(); ++I) {
      VerifyResult &Z3Result = Z3Results[I];
      VerifyResult &CVC5Result = CVC5Results[I];
      CacheHits += Z3Result.CacheHits;
      CacheMisses += Z3Result.CacheMisses;
      CacheErrors += Z3Result.CacheErrors;
      ReusedQueries += Z3Result.ReusedQueries;
      if (CacheError.empty() && !Z3Result.CacheError.empty())
        CacheError = Z3Result.CacheError;

      const bool SameObligation =
          Z3Result.ObligationId == CVC5Result.ObligationId &&
          Z3Result.ObligationType == CVC5Result.ObligationType;
      if (!SameObligation) {
        if (!FirstDisagreement) {
          FirstDisagreement =
              unresolvedPair(std::move(Z3Result), std::move(CVC5Result), false);
          FirstDisagreement->Reason = VerifyReason::InvalidBackendResult;
          FirstDisagreement->Message =
              "portfolio adapters returned differently attributed results";
        }
        continue;
      }
      const bool Z3Expected = Z3Result.Status == VerifyStatus::Verified ||
                              Z3Result.Status == VerifyStatus::Failed ||
                              Z3Result.Status == VerifyStatus::Unresolved;
      const bool CVC5Expected = CVC5Result.Status == VerifyStatus::Verified ||
                                CVC5Result.Status == VerifyStatus::Failed ||
                                CVC5Result.Status == VerifyStatus::Unresolved;
      if (!Z3Expected || !CVC5Expected) {
        if (!FirstDisagreement) {
          const std::string Statuses =
              "invalid portfolio component status: z3=" +
              statusName(Z3Result.Status).str() +
              ", cvc5=" + statusName(CVC5Result.Status).str();
          FirstDisagreement =
              unresolvedPair(std::move(Z3Result), std::move(CVC5Result), false);
          FirstDisagreement->Reason = VerifyReason::InvalidBackendResult;
          FirstDisagreement->Message = Statuses;
        }
        continue;
      }
      if (Z3Result.Status == VerifyStatus::Verified &&
          CVC5Result.Status == VerifyStatus::Verified)
        continue;
      if (Z3Result.Status == VerifyStatus::Failed &&
          CVC5Result.Status == VerifyStatus::Failed) {
        if (!FirstFailure)
          FirstFailure = std::move(Z3Result);
        continue;
      }
      if (Z3Result.Status == VerifyStatus::Unresolved ||
          CVC5Result.Status == VerifyStatus::Unresolved) {
        if (!FirstUnresolved)
          FirstUnresolved =
              unresolvedPair(std::move(Z3Result), std::move(CVC5Result), false);
        continue;
      }
      const bool Disagreement =
          isDecisive(Z3Result.Status) && isDecisive(CVC5Result.Status);
      if (!FirstDisagreement)
        FirstDisagreement = unresolvedPair(std::move(Z3Result),
                                           std::move(CVC5Result), Disagreement);
    }

    VerifyResult Result;
    if (FirstDisagreement)
      Result = std::move(*FirstDisagreement);
    else if (FirstFailure)
      Result = std::move(*FirstFailure);
    else if (FirstUnresolved)
      Result = std::move(*FirstUnresolved);
    else
      Result.Status = VerifyStatus::Verified;
    Result.BackendName = "portfolio";
    Result.CacheHits = CacheHits;
    Result.CacheMisses = CacheMisses;
    Result.CacheErrors = CacheErrors;
    Result.CacheError = std::move(CacheError);
    Result.ReusedQueries = ReusedQueries;
    return Result;
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
  case VerifyReason::SolverUnavailable:
    return "solver.unavailable";
  case VerifyReason::SolverInvocationFailure:
    return "solver.invocation-failed";
  case VerifyReason::SolverMalformedOutput:
    return "solver.malformed-output";
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
  case BackendKind::CVC5:
    return std::make_unique<CVC5VerifyBackend>(Execution);
  case BackendKind::Portfolio:
    return std::make_unique<PortfolioVerifyBackend>(Execution);
  }
  llvm_unreachable("unknown verification backend");
}
