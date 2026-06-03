//===--- VerifyBackend.cpp ------------------------------------------------===//
#include "VerifyBackend.h"
#include "LeanBackend.h"
#include "Z3Encode.h"

using namespace clang;
using namespace verify;

namespace {
class LeanVerifyBackend : public VerifyBackend {
  llvm::raw_ostream *Out;
  unsigned TimeoutMs;

public:
  explicit LeanVerifyBackend(llvm::raw_ostream *OS, unsigned TimeoutMs = 0)
      : Out(OS), TimeoutMs(TimeoutMs) {}
  llvm::StringRef getName() const override { return "lean"; }
  VerifyResult verifyPassive(const PassiveProgram &P) override {
    VerifyResult R;
    if (!Out) {
      R.Status = VerifyStatus::Unknown;
      R.Message = "no lean output stream";
      return R;
    }
    return exportLeanScratchPad(P, *Out, TimeoutMs);
  }
};

class BMCVerifyBackend : public VerifyBackend {
  std::unique_ptr<Z3VerifyBackend> Z3;

public:
  explicit BMCVerifyBackend(unsigned TimeoutMs = 0)
      : Z3(std::make_unique<Z3VerifyBackend>(TimeoutMs)) {}
  llvm::StringRef getName() const override { return "bmc"; }
  VerifyResult verifyPassive(const PassiveProgram &P) override {
    return Z3->verifyPassive(P);
  }
};
} // namespace

std::unique_ptr<VerifyBackend>
verify::createVerifyBackend(BackendKind K, llvm::raw_ostream *LeanOut,
                            unsigned /*BMCUnroll*/, unsigned SolverTimeoutMs) {
  switch (K) {
  case BackendKind::Z3:
    return std::make_unique<Z3VerifyBackend>(SolverTimeoutMs);
  case BackendKind::Lean:
    return std::make_unique<LeanVerifyBackend>(LeanOut, SolverTimeoutMs);
  case BackendKind::BMC:
    return std::make_unique<BMCVerifyBackend>(SolverTimeoutMs);
  }
  return std::make_unique<Z3VerifyBackend>(SolverTimeoutMs);
}