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
/// Twice the default: collection theories need more search.
inline constexpr unsigned DefaultCollectionTimeoutMs =
    2 * DefaultSolverTimeoutMs;
/// Ten times the default: a function runs a whole query, its obligations,
/// and their retries, so it legitimately takes several query timeouts.
inline constexpr unsigned DefaultFunctionTimeoutMs =
    10 * DefaultSolverTimeoutMs;

enum class DiagnosticFormat { Text, Json };

/// Which obligations of an unresolved module --lean-fallback exports.
enum class LeanFallbackScope {
  /// Only those the solver backend did not prove individually.
  Unproved,
  All
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
  /// Deterministic per-query solver resource limit; 0 disables it.
  unsigned SolverResourceLimit = 0;
  /// Number of isolated solver jobs. 0 selects available physical cores.
  unsigned Jobs = 1;
  /// Maximum canonical expression nodes per backend module; 0 disables it.
  uint64_t MaxQueryNodes = 0;
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
};

bool verifyTranslationUnit(ASTContext &Ctx, llvm::raw_ostream &OS,
                           const VerifyOptions &Opts = VerifyOptions());
} // namespace verify
} // namespace clang

#endif