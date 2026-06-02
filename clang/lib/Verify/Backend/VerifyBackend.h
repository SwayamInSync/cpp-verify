//===--- VerifyBackend.h - Pluggable verification backends --------------===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_VERIFYBACKEND_H
#define LLVM_CLANG_VERIFY_BACKEND_VERIFYBACKEND_H

#include "../Transform/Passivize.h"
#include <map>
#include <memory>
#include <string>

namespace clang {
namespace verify {

enum class VerifyStatus { Verified, Failed, Unknown };

struct VerifyResult {
  VerifyStatus Status = VerifyStatus::Unknown;
  std::string Message;
  std::map<std::string, std::string> Model;
};

class VerifyBackend {
public:
  virtual ~VerifyBackend() = default;
  virtual llvm::StringRef getName() const = 0;
  virtual VerifyResult verifyPassive(const PassiveProgram &P) = 0;
};

enum class BackendKind { Z3, Lean, BMC };

std::unique_ptr<VerifyBackend>
createVerifyBackend(BackendKind K, llvm::raw_ostream *LeanOut = nullptr,
                    unsigned BMCUnroll = 10);

} // namespace verify
} // namespace clang

#endif