//===--- LeanBackend.h - Lean scratch-pad export ------------------------===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_LEANBACKEND_H
#define LLVM_CLANG_VERIFY_BACKEND_LEANBACKEND_H

#include "VerifyBackend.h"
#include "llvm/Support/raw_ostream.h"
#include <map>
#include <optional>
#include <set>
#include <string>
#include <vector>

namespace clang {
namespace verify {

/// A goal of an editable Lean project, with what identifies it across
/// regenerations: the semantic hash of its obligation. Its proof file lives in
/// the directory of its function's group.
struct LeanProjectGoal {
  std::string Name;
  std::string Group;
  std::string StableId;
  std::string Hash;
  /// Where its obligation is, as a Lean comment may hold it.
  std::string Source;
  /// The prefix of the spec bodies its goal may unfold.
  std::string BodyPrefix;
  /// What a proof of its readable form introduces, in order: the goal's
  /// variables, definitions, and named hypotheses.
  std::string Intros;
  /// The names 0.1 gave the goal and its spec bodies, which a project 0.1
  /// generated still uses.
  std::string LegacyName;
  std::string LegacyBodyPrefix;
  /// False for an obligation of an exported function that a selection left
  /// to the solver: its goal is known, but has no definition or proof file.
  bool Exported = true;
};

/// The group of a module's goals in a project: its function's directory.
std::string leanProjectGroup(const ObligationModule &Module);

/// The generated modules of a Lean project: the declarations of the specs
/// its goals apply, which every goal module imports, and each group's spec
/// definitions and goals.
struct LeanProjectModules {
  std::string Specs;
  std::map<std::string, std::string> Goals;
  /// The groups in the order their functions were exported: the source's.
  std::vector<std::string> Order;
};

/// The definitions every exported goal is stated with.
void emitLeanPrelude(llvm::raw_ostream &OS, bool Project);

/// Selection names the internal IDs to export; a project goal is named by
/// its function and semantic hash, so it keeps its name whatever else is
/// exported, and a scratch-pad goal keeps the positional name it has when
/// every obligation is exported. A project records every goal of the module,
/// the ones left out as not exported. Declarations, when given, receives
/// the declarations of the specs, each once.
VerifyResult
exportLeanScratchPad(const ObligationModule &Module, llvm::raw_ostream &OS,
                     bool EmitPreamble, std::set<std::string> &EmittedFunctions,
                     std::set<std::string> &EmittedTheorems,
                     unsigned ModuleIndex,
                     std::vector<LeanProjectGoal> *ProjectGoals,
                     const std::set<std::string> *Selection = nullptr,
                     llvm::raw_ostream *Declarations = nullptr);

class LeanVerifyBackend : public VerifyBackend {
  llvm::raw_ostream *Out = nullptr;
  LeanProjectModules *Modules = nullptr;
  bool PreambleEmitted = false;
  std::set<std::string> EmittedFunctions;
  std::set<std::string> EmittedTheorems;
  unsigned ModuleIndex = 0;
  std::vector<LeanProjectGoal> *ProjectGoals;
  std::optional<std::set<std::string>> Selection;

public:
  LeanVerifyBackend(llvm::raw_ostream *OS,
                    std::vector<LeanProjectGoal> *ProjectGoals)
      : Out(OS), ProjectGoals(ProjectGoals) {}
  /// A project's export, into its modules.
  LeanVerifyBackend(LeanProjectModules *Modules,
                    std::vector<LeanProjectGoal> *ProjectGoals)
      : Modules(Modules), ProjectGoals(ProjectGoals) {}
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