//===--- VerifyBackend.h - Pluggable verification backends --------------===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_VERIFYBACKEND_H
#define LLVM_CLANG_VERIFY_BACKEND_VERIFYBACKEND_H

#include "Obligation.h"
#include <map>
#include <memory>
#include <string>

namespace clang {
namespace verify {

enum class VerifyStatus { Verified, Failed, Unknown, Exported };

struct VerifyResult {
  VerifyStatus Status = VerifyStatus::Unknown;
  std::string Message;
  std::map<std::string, std::string> Model;
  std::string ObligationId;
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
                    unsigned BMCUnroll = 10, unsigned SolverTimeoutMs = 0);

} // namespace verify
} // namespace clang

#endif