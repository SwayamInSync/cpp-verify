//===--- CVC5Backend.h - SMT-LIB and cvc5 verification ---------*- C++ -*-===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_CVC5BACKEND_H
#define LLVM_CLANG_VERIFY_BACKEND_CVC5BACKEND_H

#include "VerifyBackend.h"
#include "llvm/Support/raw_ostream.h"
#include <string>
#include <vector>

namespace clang {
namespace verify {

/// Encode one canonical query as a standalone SMT-LIB2 script.
llvm::Expected<std::string> encodeSMTLibQuery(const ObligationModule &Module,
                                              const LogicExpr *Query);

VerifyResult lowerSMTLibModule(const ObligationModule &Module,
                               llvm::raw_ostream *SMTLibOut = nullptr,
                               const BackendExecutionOptions &Execution = {});

class CVC5VerifyBackend : public VerifyBackend {
  std::string SolverPath;
  std::string SolverPathError;
  unsigned TimeoutMs;
  unsigned ResourceLimit;
  unsigned Jobs;
  uint64_t MaxQueryNodes;

  VerifyResult verifyQuery(const ObligationModule &Module,
                           const LogicExpr *Query) const;
  VerifyResult verifyObligation(const ObligationModule &Module,
                                const Obligation &Item) const;

public:
  explicit CVC5VerifyBackend(const BackendExecutionOptions &Execution = {});
  llvm::StringRef getName() const override { return "cvc5"; }
  BackendCapabilities getCapabilities() const override {
    return {allLogicFeatures(), true};
  }
  std::vector<VerifyResult>
  verifyObligations(const ObligationModule &Module) const;

protected:
  VerifyResult verifyModule(const ObligationModule &Module) override;
};

} // namespace verify
} // namespace clang

#endif
