//===--- VerifyBackend.h - Pluggable verification backends --------------===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_VERIFYBACKEND_H
#define LLVM_CLANG_VERIFY_BACKEND_VERIFYBACKEND_H

#include "Obligation.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/ThreadPool.h"
#include <chrono>
#include <cstdint>
#include <map>
#include <memory>
#include <optional>
#include <string>

namespace clang {
namespace verify {

enum class VerifyStatus {
  Lowered,
  Verified,
  Failed,
  Unresolved,
  BoundedSafe,
  Exported,
  Certified,
  /// Every obligation is proved: some by a solver backend, the rest by
  /// kernel-checked Lean proofs.
  MixedProof
};

/// Stable, backend-independent explanation for a non-success result. The
/// textual message remains diagnostic detail and is not a machine interface.
enum class VerifyReason {
  None,
  Counterexample,
  SolverTimeout,
  SolverResourceLimit,
  SolverUnknown,
  SolverUnavailable,
  SolverInvocationFailure,
  SolverMalformedOutput,
  QuerySizeLimit,
  EncodingFailure,
  InvalidObligation,
  UnsupportedLogic,
  MissingQuery,
  InvalidBackendResult,
  InconsistentBackendResults,
  IncompleteBound,
  LeanExportFailure,
  CacheCorrupt,
  CacheIOFailure,
  SpecFuel,
  SpecHidden,
  UncheckedCounterexample,
  /// The proof uses a spec whose termination is not established.
  SpecTermination,
  /// The proof uses a spec whose reads clause is not established.
  SpecReads,
  /// The proof uses a spec whose postcondition is not established.
  SpecPost,
  /// The proof uses the unfolding of an inductive predicate whose rules are
  /// not established.
  SpecInductive,
  /// The proof relies on facts whose own proofs rely on it.
  ProofCycle,
  /// An obligation stands for a construct the verifier cannot model.
  UnsupportedConstruct,
  /// The proof assumes a callee contract the callee did not establish.
  CalleeContract,
  /// A loop has no termination measure.
  DecreasesMissing
};

llvm::StringRef verifyReasonCode(VerifyReason Reason);

struct VerifyModelValue {
  std::string DisplayName;
  std::string InternalName;
  LogicSort Sort;
  ObligationSource Source;
  /// Empty when the solver model does not determine this value. Backends must
  /// not use model completion to manufacture a diagnostic value.
  std::optional<std::string> Value;
};

struct VerifyTraceValue {
  std::string Label;
  LogicSort Sort;
  std::optional<std::string> Value;
};

struct VerifyTraceEvent {
  DiagnosticTraceKind Kind = DiagnosticTraceKind::Branch;
  std::string Message;
  ObligationSource Source;
  /// Empty when the model does not determine whether this event is on the
  /// counterexample path.
  std::optional<bool> Active;
  std::vector<VerifyTraceValue> Values;
};

/// How a Lean fallback divides a module's obligations.
struct ProofEvidence {
  /// The backend whose individual proofs cover the obligations not in Lean.
  std::string Solver;
  size_t Total = 0;
  /// Obligations the solver proved individually, when it checked each one.
  std::optional<size_t> SolverProved;
  /// Public IDs of the obligations exported to Lean.
  std::vector<std::string> LeanObligations;
};

/// How often a solver instantiated one quantifier, named by its source
/// position.
struct QuantifierProfileEntry {
  unsigned Line = 0;
  unsigned Column = 0;
  uint64_t Instances = 0;
  unsigned MaxGeneration = 0;
};

struct VerifyResult {
  VerifyStatus Status = VerifyStatus::Unresolved;
  VerifyReason Reason = VerifyReason::None;
  std::string BackendName;
  std::optional<unsigned> Bound;
  std::string Message;
  std::vector<VerifyModelValue> Model;
  std::vector<VerifyTraceEvent> Trace;
  std::string ObligationId;
  std::optional<ObligationKind> ObligationType;
  SourceLocation Location;
  ObligationSource Source;
  uint64_t CacheHits = 0;
  uint64_t CacheMisses = 0;
  uint64_t CacheErrors = 0;
  std::string CacheError;
  /// Successful ordered queries reused within this process.
  uint64_t ReusedQueries = 0;
  /// Bounds actually explored by an incremental BMC source run.
  std::vector<unsigned> ExploredBounds;
  /// For an Unresolved module, the internal IDs of the obligations not proved
  /// individually; absent when the backend did not check each one.
  std::optional<std::vector<std::string>> UnprovedObligations;
  std::optional<ProofEvidence> Evidence;
  /// With --profile-quantifiers, the busiest quantifiers of an unresolved
  /// query, most instantiated first.
  std::vector<QuantifierProfileEntry> QuantifierProfile;
};

struct BackendCapabilities {
  LogicFeatureSet SupportedFeatures = 0;
  bool ProducesVerificationVerdict = true;
};

class VerifyBackend {
public:
  virtual ~VerifyBackend() = default;
  virtual llvm::StringRef getName() const = 0;
  virtual BackendCapabilities getCapabilities() const = 0;
  VerifyResult verify(const ObligationModule &Module);
  /// Queries started after this get only the time left before Deadline: one
  /// function's budget, shared by its queries. Unset removes the limit.
  virtual void
  setDeadline(std::optional<std::chrono::steady_clock::time_point> Deadline) {}

protected:
  virtual VerifyResult verifyModule(const ObligationModule &Module) = 0;
};

enum class BackendKind { Z3, Lean, BMC, CVC5, Portfolio };

/// Solver representation of C++ machine integers. Every choice is exact.
enum class MachineIntegerEncoding {
  /// Integer unless the query needs the bits of a non-constant operand.
  Auto,
  /// The value in the sort's range; operations reduce modulo 2^w.
  Integer,
  BitVector
};

llvm::StringRef machineIntegerEncodingName(MachineIntegerEncoding Encoding);
std::optional<MachineIntegerEncoding>
parseMachineIntegerEncoding(llvm::StringRef Name);

struct BackendExecutionOptions {
  unsigned SolverTimeoutMs = 0;
  /// Per-query timeout for modules over sequences, sets, multisets, or
  /// maps; unset means SolverTimeoutMs.
  std::optional<unsigned> CollectionTimeoutMs;
  /// Per-query deterministic solver resource limit; 0 disables it.
  unsigned SolverResourceLimit = 0;
  /// Isolated solver jobs. 0 selects the available physical-core count.
  unsigned Jobs = 1;
  /// The workers obligations run on, shared with the driver's function tasks
  /// so that exactly Jobs run at once; null gives each call its own.
  llvm::ThreadPoolInterface *Pool = nullptr;
  /// Maximum canonical expression nodes in a module; 0 disables it.
  uint64_t MaxQueryNodes = 0;
  MachineIntegerEncoding IntegerEncoding = MachineIntegerEncoding::Auto;
  /// Do not retry a whole-module query after individual obligations are
  /// unresolved. Interactive fallback backends can consume those unresolved
  /// obligations without spending a second whole-module timeout budget.
  bool SkipWholeModuleRetry = false;
  /// Solve the whole-module query once, at the full budget, and report it:
  /// no per-obligation queries, refinement fallback, or induction. For small
  /// auxiliary questions such as the vacuity checks.
  bool SingleQuery = false;
  /// Optional cvc5 executable. An empty path searches PATH for `cvc5`.
  std::string CVC5Path;
  /// After an unresolved quantified Z3 query, count each quantifier's
  /// instantiations in a profiling rerun.
  bool ProfileQuantifiers = false;
  std::string ProofCachePath;
  uint64_t ProofCacheMaxBytes = 1024ULL * 1024ULL * 1024ULL;
  uint64_t ProofCacheMaxEntries = 100000;
};

/// \p Ms, or the time left before \p Deadline when that is less (at least
/// one millisecond); 0 means no limit.
inline unsigned
withinDeadline(unsigned Ms,
               std::optional<std::chrono::steady_clock::time_point> Deadline) {
  if (!Deadline)
    return Ms;
  const auto Left = std::chrono::duration_cast<std::chrono::milliseconds>(
                        *Deadline - std::chrono::steady_clock::now())
                        .count();
  const unsigned Remaining =
      Left <= 1 ? 1U
                : static_cast<unsigned>(std::min<long long>(Left, UINT32_MAX));
  return Ms == 0 ? Remaining : std::min(Ms, Remaining);
}

/// The per-query timeout for \p Module: the collection timeout when it
/// reasons about collections, whose theories need more search.
inline unsigned moduleTimeoutMs(const ObligationModule &Module,
                                unsigned SolverTimeoutMs,
                                std::optional<unsigned> CollectionTimeoutMs) {
  const bool OverCollections =
      Module.RequiredFeatures & (logicFeature(LogicFeature::Sequences) |
                                 logicFeature(LogicFeature::Collections));
  return OverCollections && CollectionTimeoutMs ? *CollectionTimeoutMs
                                                : SolverTimeoutMs;
}

std::unique_ptr<VerifyBackend>
createVerifyBackend(BackendKind K, llvm::raw_ostream *LeanOut = nullptr,
                    unsigned BMCUnroll = 10,
                    const BackendExecutionOptions &Execution = {},
                    std::vector<std::string> *LeanProjectGoals = nullptr);

VerifyResult
lowerObligationModule(const ObligationModule &Module,
                      llvm::raw_ostream *Z3Out = nullptr,
                      const BackendExecutionOptions &Execution = {});

} // namespace verify
} // namespace clang

#endif