//===--- VerifyBackend.h - Pluggable verification backends --------------===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_VERIFYBACKEND_H
#define LLVM_CLANG_VERIFY_BACKEND_VERIFYBACKEND_H

#include "Obligation.h"
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

struct VerifyResult {
  VerifyStatus Status = VerifyStatus::Unresolved;
  std::string BackendName;
  std::optional<unsigned> Bound;
  std::string Message;
  std::map<std::string, std::string> Model;
  std::string ObligationId;
  std::optional<ObligationKind> ObligationType;
  SourceLocation Location;
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

} // namespace verify
} // namespace clang

#endif