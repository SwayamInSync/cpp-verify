//===--- LeanBackend.h - Lean scratch-pad export ------------------------===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_LEANBACKEND_H
#define LLVM_CLANG_VERIFY_BACKEND_LEANBACKEND_H

#include "VerifyBackend.h"
#include "llvm/Support/raw_ostream.h"
#include <optional>
#include <set>
#include <vector>

namespace clang {
namespace verify {

/// Selection names the internal IDs to export; an exported goal keeps the
/// positional name it has when every obligation is exported.
VerifyResult
exportLeanScratchPad(const ObligationModule &Module, llvm::raw_ostream &OS,
                     bool EmitPreamble, std::set<std::string> &EmittedFunctions,
                     std::set<std::string> &EmittedTheorems,
                     unsigned ModuleIndex,
                     std::vector<std::string> *ProjectGoals,
                     const std::set<std::string> *Selection = nullptr);

class LeanVerifyBackend : public VerifyBackend {
  llvm::raw_ostream *Out;
  bool PreambleEmitted = false;
  std::set<std::string> EmittedFunctions;
  std::set<std::string> EmittedTheorems;
  unsigned ModuleIndex = 0;
  std::vector<std::string> *ProjectGoals;
  std::optional<std::set<std::string>> Selection;

public:
  LeanVerifyBackend(llvm::raw_ostream *OS,
                    std::vector<std::string> *ProjectGoals)
      : Out(OS), ProjectGoals(ProjectGoals) {}
  llvm::StringRef getName() const override { return "lean"; }
  BackendCapabilities getCapabilities() const override {
    // Collections have no Lean semantics yet.
    return {allLogicFeatures() & ~logicFeature(LogicFeature::Sequences) &
                ~logicFeature(LogicFeature::Collections),
            false};
  }
  /// Restrict later exports to these internal obligation IDs.
  void selectObligations(std::optional<std::set<std::string>> Ids) {
    Selection = std::move(Ids);
  }

protected:
  VerifyResult verifyModule(const ObligationModule &Module) override;
};

} // namespace verify
} // namespace clang

#endif