//===--- Verifier.h -------------------------------------------------------===//
#ifndef LLVM_CLANG_VERIFY_DRIVER_VERIFIER_H
#define LLVM_CLANG_VERIFY_DRIVER_VERIFIER_H

#include "../Backend/VerifyBackend.h"
#include "llvm/Support/raw_ostream.h"
#include <map>
#include <memory>
#include <string>
#include <vector>

namespace clang {
class ASTContext;

namespace verify {
inline constexpr unsigned DefaultSolverTimeoutMs = 30000;
/// cppverify_auto proves 99.8% of the suite's goals it proves within 5 s.
inline constexpr unsigned DefaultLeanAutoTimeoutMs = 20000;
/// Twice the default: collection theories need more search.
inline constexpr unsigned DefaultCollectionTimeoutMs =
    2 * DefaultSolverTimeoutMs;
/// Ten times the default: a function runs a whole query, its obligations,
/// and their retries, so it legitimately takes several query timeouts.
inline constexpr unsigned DefaultFunctionTimeoutMs =
    10 * DefaultSolverTimeoutMs;
/// The distinct expression nodes built for one function's proof obligations:
/// a node takes about 600 bytes, and Z3's encoding of it about five times
/// that, and the largest function of the test suite (safe_fib.cpp's
/// iterative_fibonacci) has 375,000.
inline constexpr uint64_t DefaultMaxQueryNodes = 4000000;
/// The megabytes Z3's queries may allocate together, and each cvc5 process.
inline constexpr uint64_t DefaultMemoryLimitMB = 8192;

enum class DiagnosticFormat { Text, Json };

/// Which obligations of an unresolved module --lean-fallback exports.
enum class LeanFallbackScope {
  /// Only those the solver backend did not prove individually.
  Unproved,
  All
};

/// The verdicts a run reported, counted for its summary line.
struct VerifySummary {
  unsigned Verified = 0;
  unsigned Failed = 0;
  unsigned Unresolved = 0;
  unsigned BoundedSafe = 0;
  unsigned Trusted = 0;
  unsigned Lowered = 0;
  unsigned Exported = 0;
  unsigned Interrupted = 0;
  /// The reason code of each unresolved verdict, counted.
  std::map<std::string, unsigned> Reasons;
};

struct VerifyOptions {
  unsigned DumpIRLayers = 0;
  /// Build and encode verification conditions without invoking a solver.
  bool LowerOnly = false;
  BackendKind Backend = BackendKind::Z3;
  std::string LeanOutPath;
  std::string LeanProjectPath;
  std::string LeanFallbackProjectPath;
  LeanFallbackScope LeanScope = LeanFallbackScope::Unproved;
  bool LeanCertify = false;
  /// Delete the proofs a Lean project keeps in Stale/ once regenerated.
  bool LeanPruneStale = false;
  /// Try cppverify_auto on each new goal of a Lean project, each for at most
  /// LeanAutoTimeoutMs of wall-clock time (0: no limit).
  bool LeanAuto = true;
  unsigned LeanAutoTimeoutMs = DefaultLeanAutoTimeoutMs;
  /// The Lean processes automation and certification run at once (0: the
  /// available physical cores).
  unsigned LeanJobs = 0;
  unsigned BMCUnroll = 10;
  /// Per-query solver timeout in milliseconds; 0 disables it. Non-terminating
  /// queries return Unknown instead of hanging the tool.
  unsigned SolverTimeoutMs = DefaultSolverTimeoutMs;
  /// Per-query timeout for queries over sequences, sets, multisets, or maps.
  unsigned CollectionTimeoutMs = DefaultCollectionTimeoutMs;
  /// The time all queries of one function may take together: a whole query,
  /// its obligations, and their retries and induction attempts; 0 disables
  /// it.
  unsigned FunctionTimeoutMs = DefaultFunctionTimeoutMs;
  /// The time one counterexample check may take: unset, half the query
  /// timeout; 0, the query's own time.
  std::optional<unsigned> CertifyTimeoutMs;
  /// Deterministic per-query solver resource limit; 0 disables it.
  unsigned SolverResourceLimit = 0;
  /// Number of isolated solver jobs. 0 selects available physical cores.
  unsigned Jobs = 1;
  /// Maximum canonical expression nodes per module, checked as it is built
  /// and before a backend runs it; 0 disables it.
  uint64_t MaxQueryNodes = DefaultMaxQueryNodes;
  /// The megabytes Z3's queries may allocate together, and each cvc5
  /// process; 0 disables the limit.
  uint64_t MemoryLimitMB = DefaultMemoryLimitMB;
  /// Solver representation of machine integers (Z3, cvc5, portfolio, BMC).
  MachineIntegerEncoding IntegerEncoding = MachineIntegerEncoding::Auto;
  /// Optional cvc5 executable for cvc5 and strict portfolio verification.
  std::string CVC5Path;
  /// Optional persistent cache of successful dependency-scoped proofs.
  std::string ProofCachePath;
  uint64_t ProofCacheMaxBytes = 1024ULL * 1024ULL * 1024ULL;
  uint64_t ProofCacheMaxEntries = 100000;
  /// Check every memory access and pointer step against the object it may
  /// address: a parameter's declared valid(p, n) extent or its single
  /// pointee. Core expression definedness checks are always emitted during
  /// passivization.
  bool CheckUB = true;
  /// Report how often each quantifier of an unresolved query is instantiated.
  bool ProfileQuantifiers = false;
  /// Human-readable diagnostics or versioned JSON Lines records.
  DiagnosticFormat Diagnostics = DiagnosticFormat::Text;
  /// Optional versioned binary archive for backend-neutral obligation modules.
  llvm::raw_ostream *ObligationOut = nullptr;
  /// Print only what is not a proof: failures, unresolved results, errors,
  /// and warnings.
  bool Quiet = false;
  /// Print the spec functions that need no check (`spec axiom`) too.
  bool Verbose = false;
  /// List the functions the run would verify, and verify none.
  bool ListFunctions = false;
  /// Report where each function's verification spent its time.
  bool TimeReport = false;
  /// Show which functions are done on standard error as they finish; unset,
  /// when standard error is a terminal.
  std::optional<bool> Progress;
  /// How many failing obligations of a function are reported, each with its
  /// own counterexample (Z3 only); 0 reports every one.
  unsigned MaxFailures = 1;
  /// Glob patterns over function names: only the functions they match are
  /// reported. Empty: every function.
  std::vector<std::string> FunctionPatterns;
  /// For a failure whose counterexample passes through a loop, the most
  /// iterations of each loop that unrolling may try to find an execution
  /// that fails (0: do not try).
  unsigned ConfirmBound = 10;
  /// Where the run counts the verdicts it prints, if anywhere.
  VerifySummary *Summary = nullptr;
  /// A run over several files, which holds each file's results until every
  /// file is verified (see CrossFileRun), or null.
  class CrossFileRun *CrossFile = nullptr;
  /// Where to write the contracts this file verifies and those it assumes
  /// from other files, for checkContracts. With it, a contract declared
  /// without a definition holds for now, and a proof that rests on it says
  /// so ([assumes=...]): the check of the files together settles it.
  std::string ContractsOut;
};

/// One run over several files. A contract that a file declares without a
/// definition may be defined and verified in another file of the run, so a
/// proof that rests on it waits: each file's results are kept, and once
/// every file is verified, a proof stands where every such contract it rests
/// on is established by its definition's verification, and is otherwise
/// unresolved (callee.contract), as within one file.
class CrossFileRun {
public:
  CrossFileRun();
  ~CrossFileRun();
  CrossFileRun(const CrossFileRun &) = delete;
  CrossFileRun &operator=(const CrossFileRun &) = delete;

  /// Settles the contracts the files assume against those they verify,
  /// prints each file's results in the order the files were verified, and
  /// counts them into \p Summary when it is given. Returns how many files
  /// do not succeed.
  unsigned finish(llvm::raw_ostream &OS, VerifySummary *Summary);

  struct Impl;
  std::unique_ptr<Impl> State;
};

/// The check of files verified apart (their ContractsOut records): every
/// contract a file assumes must be established by the verification of its
/// definition in another file. Prints each proof that rests on one that is
/// not, and returns how many.
unsigned checkContracts(const std::vector<std::string> &Paths,
                        llvm::raw_ostream &OS);

/// Verifies the translation unit. In a run over several files
/// (Opts.CrossFile), the results wait for CrossFileRun::finish, and the
/// result is the file's as far as it alone decides.
bool verifyTranslationUnit(ASTContext &Ctx, llvm::raw_ostream &OS,
                           const VerifyOptions &Opts = VerifyOptions());

/// What exporting the modules of an archive to a Lean project gives: a
/// result for each module, in order, with the goals cppverify_auto proves of
/// it, and what the project warns of; or why the project was not written.
struct LeanProjectReplay {
  std::vector<VerifyResult> Results;
  std::vector<unsigned> Automatic;
  std::vector<std::string> Warnings;
  std::string Error;
};

/// Exports Modules to the Lean project of Opts as a source run exports its
/// functions, with their proofs and cppverify_auto, and with LeanCertify
/// certifies them. A module alone is all that is checked: one whose goals
/// all certify is Verified, its obligations proved; a bounded one is
/// BoundedSafe when only unwinding goals do not.
LeanProjectReplay
replayLeanProject(const std::vector<ObligationModule> &Modules,
                  const VerifyOptions &Opts);
} // namespace verify
} // namespace clang

#endif