//===--- VerifyBackend.h - Pluggable verification backends --------------===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_VERIFYBACKEND_H
#define LLVM_CLANG_VERIFY_BACKEND_VERIFYBACKEND_H

#include "Obligation.h"
#include "llvm/ADT/StringRef.h"
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
  Certified
};

/// Stable, backend-independent explanation for a non-success result. The
/// textual message remains diagnostic detail and is not a machine interface.
enum class VerifyReason {
  None,
  Counterexample,
  SolverTimeout,
  SolverUnknown,
  EncodingFailure,
  InvalidObligation,
  UnsupportedLogic,
  MissingQuery,
  InvalidBackendResult,
  InconsistentBackendResults,
  IncompleteBound,
  LeanExportFailure
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

protected:
  virtual VerifyResult verifyModule(const ObligationModule &Module) = 0;
};

enum class BackendKind { Z3, Lean, BMC };

std::unique_ptr<VerifyBackend>
createVerifyBackend(BackendKind K, llvm::raw_ostream *LeanOut = nullptr,
                    unsigned BMCUnroll = 10, unsigned SolverTimeoutMs = 0,
                    std::vector<std::string> *LeanProjectGoals = nullptr);

VerifyResult lowerObligationModule(const ObligationModule &Module,
                                   llvm::raw_ostream *Z3Out = nullptr,
                                   unsigned SolverTimeoutMs = 0);

} // namespace verify
} // namespace clang

#endif