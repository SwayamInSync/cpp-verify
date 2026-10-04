//===--- VerifyBackend.cpp ------------------------------------------------===//
#include "VerifyBackend.h"
#include "CVC5Backend.h"
#include "Induction.h"
#include "LeanBackend.h"
#include "ObligationSimplify.h"
#include "Z3Encode.h"
#include "llvm/ADT/ScopeExit.h"
#include <set>
#include <thread>

using namespace clang;
using namespace verify;

VerifyResult LeanVerifyBackend::verifyModule(const ObligationModule &Module) {
  VerifyResult R;
  if (!Out) {
    R.Status = VerifyStatus::Unresolved;
    R.Reason = VerifyReason::LeanExportFailure;
    R.Message = "no lean output stream";
    return R;
  }
  VerifyResult Result = exportLeanScratchPad(
      Module, *Out, !PreambleEmitted, EmittedFunctions, EmittedTheorems,
      ++ModuleIndex, ProjectGoals, Selection ? &*Selection : nullptr);
  PreambleEmitted = true;
  return Result;
}

namespace {
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
  std::optional<unsigned>
  queryTimeoutMs(const ObligationModule &Module) const override {
    return Z3->queryTimeoutMs(Module);
  }
  BackendCapabilities getCapabilities() const override {
    return {allLogicFeatures(), true};
  }

protected:
  void applyDeadline(
      std::optional<std::chrono::steady_clock::time_point> D) override {
    Z3->setDeadline(D);
  }
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
        // One that only induction can settle is the one an induction over
        // the module is tried for.
        if (!FirstUnresolved ||
            (FirstUnresolved->Reason != VerifyReason::SpecFuel &&
             Result.Reason == VerifyReason::SpecFuel))
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
    case VerifyStatus::MixedProof:
      return "mixed-proof";
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
  std::optional<unsigned>
  queryTimeoutMs(const ObligationModule &Module) const override {
    return Z3->queryTimeoutMs(Module);
  }
  BackendCapabilities getCapabilities() const override {
    return {Z3->getCapabilities().SupportedFeatures &
                CVC5->getCapabilities().SupportedFeatures,
            true};
  }

protected:
  void applyDeadline(
      std::optional<std::chrono::steady_clock::time_point> D) override {
    Z3->setDeadline(D);
    CVC5->setDeadline(D);
  }
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
      Z3Results.push_back(Z3->verifyDirect(Module));
      CVC5Results.push_back(CVC5->verifyDirect(Module));
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
    std::optional<std::vector<std::string>> Unproved;
    if (Z3Results.size() == Module.Obligations.size()) {
      Unproved.emplace();
      for (size_t I = 0; I != Z3Results.size(); ++I) {
        if (Z3Results[I].ObligationId != CVC5Results[I].ObligationId) {
          Unproved.reset();
          break;
        }
        if (Z3Results[I].Status != VerifyStatus::Verified ||
            CVC5Results[I].Status != VerifyStatus::Verified)
          Unproved->push_back(Module.Obligations[I].Id);
      }
    }
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
    if (Result.Status == VerifyStatus::Unresolved)
      Result.UnprovedObligations = std::move(Unproved);
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

llvm::StringRef
verify::machineIntegerEncodingName(MachineIntegerEncoding Encoding) {
  switch (Encoding) {
  case MachineIntegerEncoding::Auto:
    return "auto";
  case MachineIntegerEncoding::Integer:
    return "integer";
  case MachineIntegerEncoding::BitVector:
    return "bitvector";
  }
  llvm_unreachable("unknown machine-integer encoding");
}

std::optional<MachineIntegerEncoding>
verify::parseMachineIntegerEncoding(llvm::StringRef Name) {
  if (Name == "auto")
    return MachineIntegerEncoding::Auto;
  if (Name == "integer")
    return MachineIntegerEncoding::Integer;
  if (Name == "bitvector")
    return MachineIntegerEncoding::BitVector;
  return std::nullopt;
}

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
  case VerifyReason::SpecFuel:
    return "spec.fuel";
  case VerifyReason::SpecHidden:
    return "spec.hidden";
  case VerifyReason::UncheckedCounterexample:
    return "counterexample.unchecked";
  case VerifyReason::SpecTermination:
    return "spec.termination";
  case VerifyReason::SpecReads:
    return "spec.reads";
  case VerifyReason::SpecPost:
    return "spec.post";
  case VerifyReason::SpecInductive:
    return "spec.inductive";
  case VerifyReason::ProofCycle:
    return "proof.cycle";
  case VerifyReason::UnsupportedConstruct:
    return "construct.unsupported";
  case VerifyReason::CalleeContract:
    return "callee.contract";
  case VerifyReason::DecreasesMissing:
    return "decreases.missing";
  }
  llvm_unreachable("unknown verification reason");
}

VerifyResult VerifyBackend::verify(const ObligationModule &Module) {
  VerifyResult Result = verifyDirect(Module);
  if (Module.Attempt != ModuleAttempt::Primary ||
      Result.Status != VerifyStatus::Unresolved ||
      (Result.Reason != VerifyReason::SpecFuel && !Result.InductionOnly))
    return Result;
  // No finite unfolding settles the module: a proof of the claim under an
  // induction hypothesis proves it everywhere. Inductions settle proofs only:
  // a model of one satisfies hypotheses foreign to the program, which keeps
  // its counterexample from being attributed and shown, and the module's own
  // counterexamples are found, checked, and confirmed by proof without it.
  // All of a module's inductions share two attempts' slices of its budget,
  // the most specific schemes first.
  const std::optional<std::chrono::steady_clock::time_point> Saved =
      FunctionDeadline;
  std::optional<std::chrono::steady_clock::time_point> Until = Saved;
  if (std::optional<unsigned> Query = queryTimeoutMs(Module)) {
    const auto Cap = std::chrono::steady_clock::now() +
                     std::chrono::milliseconds(2 * attemptBudgetMs(*Query));
    if (!Until || Cap < *Until)
      Until = Cap;
  }
  setDeadline(Until);
  llvm::scope_exit Restore([&] { setDeadline(Saved); });
  std::vector<std::string> Tried;
  for (const InductionScheme &Scheme : inductionSchemes(Module)) {
    if (Until && std::chrono::steady_clock::now() >= *Until)
      break;
    auto Inductive = inductionModule(Module, Scheme);
    if (!Inductive) {
      llvm::consumeError(Inductive.takeError());
      continue;
    }
    Tried.push_back(Scheme.Description);
    VerifyResult Attempt = verifyDirect(*Inductive);
    if (Attempt.Status != VerifyStatus::Verified &&
        Attempt.Status != VerifyStatus::BoundedSafe)
      continue;
    Attempt.InductionUsed = Scheme.Description;
    // Its obligations rest on one another through the hypothesis.
    Attempt.UnprovedObligations.reset();
    Attempt.CacheHits += Result.CacheHits;
    Attempt.CacheMisses += Result.CacheMisses;
    Attempt.CacheErrors += Result.CacheErrors;
    if (Attempt.CacheError.empty())
      Attempt.CacheError = Result.CacheError;
    Attempt.ReusedQueries += Result.ReusedQueries;
    Attempt.ExploredBounds = Result.ExploredBounds;
    return Attempt;
  }
  Result.InductionTried = std::move(Tried);
  return Result;
}

VerifyResult VerifyBackend::verifyDirect(const ObligationModule &Module) {
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
  // A step toward settling another module (an induction, a confirmation)
  // gets a slice of that module's budget, for all its queries together.
  std::optional<std::chrono::steady_clock::time_point> Limit = FunctionDeadline;
  if (Module.Attempt != ModuleAttempt::Primary)
    if (std::optional<unsigned> Query = queryTimeoutMs(Module)) {
      const auto Slice = std::chrono::steady_clock::now() +
                         std::chrono::milliseconds(attemptBudgetMs(*Query));
      if (!Limit || Slice < *Limit)
        Limit = Slice;
    }
  if (Limit != FunctionDeadline)
    applyDeadline(Limit);
  llvm::scope_exit Restore([&] {
    if (Limit != FunctionDeadline)
      applyDeadline(FunctionDeadline);
  });
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
  // A model of `false` says nothing about the program.
  if (Result.Status == VerifyStatus::Failed && Result.ObligationType &&
      *Result.ObligationType == ObligationKind::Unsupported) {
    Result.Status = VerifyStatus::Unresolved;
    Result.Reason = VerifyReason::UnsupportedConstruct;
    Result.Message = "the verifier cannot model a construct here";
    for (const Obligation &Item : Module.Obligations)
      if ((Item.Id == Result.ObligationId ||
           Item.StableId == Result.ObligationId) &&
          !Item.Note.empty())
        Result.Message += ": " + Item.Note;
    Result.Model.clear();
    Result.Trace.clear();
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

/// Z3 and cvc5 at once, as Frama-C's prover list: the first proof or
/// certified counterexample stands and stops the other. Where neither
/// settles the module, the obligations each proved are joined: every
/// obligation is a query of its own, so proofs by different solvers compose.
class RaceVerifyBackend : public VerifyBackend {
  std::unique_ptr<Z3VerifyBackend> Z3;
  std::unique_ptr<CVC5VerifyBackend> CVC5;
  uint64_t MaxQueryNodes;

  static bool isDecisive(VerifyStatus Status) {
    return Status == VerifyStatus::Verified || Status == VerifyStatus::Failed;
  }

public:
  explicit RaceVerifyBackend(const BackendExecutionOptions &Execution)
      : Z3(std::make_unique<Z3VerifyBackend>(Execution, "z3")),
        CVC5(std::make_unique<CVC5VerifyBackend>(Execution)),
        MaxQueryNodes(Execution.MaxQueryNodes) {}

  llvm::StringRef getName() const override { return "race"; }
  std::optional<unsigned>
  queryTimeoutMs(const ObligationModule &Module) const override {
    return Z3->queryTimeoutMs(Module);
  }
  void cancel() override {
    Z3->cancel();
    CVC5->cancel();
  }
  void resume() override {
    Z3->resume();
    CVC5->resume();
  }
  BackendCapabilities getCapabilities() const override {
    return {Z3->getCapabilities().SupportedFeatures |
                CVC5->getCapabilities().SupportedFeatures,
            true};
  }

protected:
  void applyDeadline(
      std::optional<std::chrono::steady_clock::time_point> D) override {
    Z3->setDeadline(D);
    CVC5->setDeadline(D);
  }
  VerifyResult verifyModule(const ObligationModule &Module) override {
    if (MaxQueryNodes != 0 &&
        obligationModuleNodeCount(Module) > MaxQueryNodes) {
      VerifyResult Result;
      Result.Status = VerifyStatus::Unresolved;
      Result.Reason = VerifyReason::QuerySizeLimit;
      Result.Message =
          "canonical obligation module exceeds query node budget " +
          std::to_string(MaxQueryNodes);
      Result.BackendName = "race";
      return Result;
    }
    resume();
    VerifyResult Z3Result;
    VerifyResult CVC5Result;
    std::thread Other([&] {
      CVC5Result = CVC5->verifyDirect(Module);
      if (isDecisive(CVC5Result.Status))
        Z3->cancel();
    });
    Z3Result = Z3->verifyDirect(Module);
    if (isDecisive(Z3Result.Status))
      CVC5->cancel();
    Other.join();
    resume();
    Z3Result.BackendName = "z3";
    CVC5Result.BackendName = "cvc5";
    const bool Z3Decides = isDecisive(Z3Result.Status);
    const bool CVC5Decides = isDecisive(CVC5Result.Status);
    if (Z3Decides && CVC5Decides && Z3Result.Status != CVC5Result.Status) {
      VerifyResult Result;
      Result.Status = VerifyStatus::Unresolved;
      Result.Reason = VerifyReason::InconsistentBackendResults;
      Result.Message =
          std::string("backend disagreement: z3=") +
          (Z3Result.Status == VerifyStatus::Verified ? "verified" : "failed") +
          ", cvc5=" +
          (CVC5Result.Status == VerifyStatus::Verified ? "verified" : "failed");
      Result.BackendName = "race";
      return Result;
    }
    if (Z3Decides)
      return Z3Result;
    if (CVC5Decides)
      return CVC5Result;
    // Neither settled the module: an obligation either proved is proved.
    if (Z3Result.UnprovedObligations && CVC5Result.UnprovedObligations) {
      std::set<std::string> CVC5Left(CVC5Result.UnprovedObligations->begin(),
                                     CVC5Result.UnprovedObligations->end());
      std::vector<std::string> Left;
      for (const std::string &Id : *Z3Result.UnprovedObligations)
        if (CVC5Left.count(Id))
          Left.push_back(Id);
      if (Left.empty()) {
        VerifyResult Result;
        Result.Status = VerifyStatus::Verified;
        Result.BackendName = "z3+cvc5";
        return Result;
      }
      Z3Result.UnprovedObligations = std::move(Left);
    }
    return Z3Result;
  }
};

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
  case BackendKind::Race:
    return std::make_unique<RaceVerifyBackend>(Execution);
  }
  llvm_unreachable("unknown verification backend");
}
