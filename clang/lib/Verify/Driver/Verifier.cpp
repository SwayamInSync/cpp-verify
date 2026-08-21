//===--- Verifier.cpp - CppVerify driver ----------------------------------===//
#include "Verifier.h"
#include "../Backend/CVC5Backend.h"
#include "../Backend/Obligation.h"
#include "../Backend/ObligationLowering.h"
#include "../Backend/ObligationSerialization.h"
#include "../Backend/ObligationSimplify.h"
#include "../Frontend/ASTConverter.h"
#include "../IR/VStmt.h"
#include "../Transform/LoopUnroll.h"
#include "../Transform/Ownership.h"
#include "../Transform/Passivize.h"
#include "../Transform/SpecInline.h"
#include "../Transform/UBChecks.h"
#include "DumpIR.h"
#include "clang/AST/ASTContext.h"
#include "clang/Basic/SourceManager.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/FormatVariadic.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/MD5.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/Program.h"
#include "llvm/Support/raw_ostream.h"
#include <iterator>
#include <optional>

using namespace clang;
using namespace verify;

namespace {

static bool isDeductiveBackend(BackendKind Kind) {
  return Kind == BackendKind::Z3 || Kind == BackendKind::CVC5 ||
         Kind == BackendKind::Portfolio;
}

static VerifyResult lowerForBackend(const ObligationModule &Module,
                                    BackendKind Kind,
                                    const BackendExecutionOptions &Execution) {
  if (Kind == BackendKind::CVC5)
    return lowerSMTLibModule(Module, nullptr, Execution);
  if (Kind == BackendKind::Portfolio) {
    VerifyResult Z3Result = lowerObligationModule(Module, nullptr, Execution);
    if (Z3Result.Status != VerifyStatus::Lowered) {
      Z3Result.BackendName = "portfolio";
      Z3Result.Message =
          "z3 component" +
          (Z3Result.Message.empty() ? std::string() : ": " + Z3Result.Message);
      return Z3Result;
    }
    VerifyResult CVC5Result = lowerSMTLibModule(Module, nullptr, Execution);
    if (CVC5Result.Status != VerifyStatus::Lowered) {
      CVC5Result.BackendName = "portfolio";
      CVC5Result.Message = "cvc5 component" + (CVC5Result.Message.empty()
                                                   ? std::string()
                                                   : ": " + CVC5Result.Message);
      return CVC5Result;
    }
    VerifyResult Result;
    Result.Status = VerifyStatus::Lowered;
    Result.BackendName = "portfolio";
    return Result;
  }
  return lowerObligationModule(Module, nullptr, Execution);
}

struct VerifyDiagnostic {
  enum Kind {
    Lowered,
    Verified,
    Error,
    Unresolved,
    BoundedSafe,
    Exported,
    Certified,
    Warning
  };
  Kind K;
  std::string Message;
  SourceLocation Loc;
  std::string FunctionName;
  std::optional<VerifyResult> Result;
};

static std::string backendSuffix(const VerifyResult &Result) {
  std::string Suffix;
  if (!Result.BackendName.empty()) {
    Suffix = " [backend=" + Result.BackendName;
    if (Result.Bound)
      Suffix += ", bound=" + std::to_string(*Result.Bound);
    Suffix += "]";
  }
  if (Result.CacheHits || Result.CacheMisses || Result.CacheErrors) {
    Suffix += " [cache=" + std::to_string(Result.CacheHits) + "/" +
              std::to_string(Result.CacheHits + Result.CacheMisses +
                             Result.CacheErrors);
    if (Result.CacheErrors)
      Suffix += ", errors=" + std::to_string(Result.CacheErrors);
    Suffix += "]";
  }
  if (!Result.CacheError.empty())
    Suffix += " [cache-error=" + Result.CacheError + "]";
  if (Result.Reason != VerifyReason::None)
    Suffix += " [reason=" + verifyReasonCode(Result.Reason).str() + "]";
  if (Result.ExploredBounds.size() > 1) {
    Suffix += " [bounds=";
    for (size_t I = 0; I != Result.ExploredBounds.size(); ++I) {
      if (I != 0)
        Suffix += ",";
      Suffix += std::to_string(Result.ExploredBounds[I]);
    }
    Suffix += "]";
  }
  if (Result.ReusedQueries)
    Suffix += " [reused-queries=" + std::to_string(Result.ReusedQueries) + "]";
  return Suffix;
}

static llvm::StringRef diagnosticKindCode(VerifyDiagnostic::Kind Kind) {
  switch (Kind) {
  case VerifyDiagnostic::Lowered:
    return "lowered";
  case VerifyDiagnostic::Verified:
    return "verified";
  case VerifyDiagnostic::Error:
    return "error";
  case VerifyDiagnostic::Unresolved:
    return "unresolved";
  case VerifyDiagnostic::BoundedSafe:
    return "bounded-safe";
  case VerifyDiagnostic::Exported:
    return "exported";
  case VerifyDiagnostic::Certified:
    return "certified";
  case VerifyDiagnostic::Warning:
    return "warning";
  }
  return "error";
}

static llvm::StringRef verifyStatusCode(VerifyStatus Status) {
  switch (Status) {
  case VerifyStatus::Lowered:
    return "lowered";
  case VerifyStatus::Verified:
    return "verified";
  case VerifyStatus::Failed:
    return "failed";
  case VerifyStatus::Unresolved:
    return "unresolved";
  case VerifyStatus::BoundedSafe:
    return "bounded-safe";
  case VerifyStatus::Exported:
    return "exported";
  case VerifyStatus::Certified:
    return "certified";
  }
  return "unresolved";
}

static llvm::StringRef obligationKindCode(ObligationKind Kind) {
  switch (Kind) {
  case ObligationKind::Assertion:
    return "assertion";
  case ObligationKind::Postcondition:
    return "postcondition";
  case ObligationKind::Unwinding:
    return "unwinding";
  }
  return "assertion";
}

static llvm::StringRef traceKindCode(DiagnosticTraceKind Kind) {
  switch (Kind) {
  case DiagnosticTraceKind::Branch:
    return "branch";
  case DiagnosticTraceKind::Call:
    return "call";
  case DiagnosticTraceKind::Loop:
    return "loop";
  case DiagnosticTraceKind::HeapWrite:
    return "heap-write";
  case DiagnosticTraceKind::Allocation:
    return "allocation";
  case DiagnosticTraceKind::LifetimeEnd:
    return "lifetime-end";
  case DiagnosticTraceKind::Deallocation:
    return "deallocation";
  case DiagnosticTraceKind::Return:
    return "return";
  }
  return "branch";
}

static std::string jsonText(llvm::StringRef Text) {
  return llvm::json::isUTF8(Text) ? Text.str() : llvm::json::fixUTF8(Text);
}

static llvm::json::Object sourceJSON(const ObligationSource &Source) {
  llvm::json::Object Result;
  if (!Source.isValid())
    return Result;
  Result["file"] = jsonText(Source.File);
  Result["line"] = Source.Line;
  Result["column"] = Source.Column;
  Result["end_line"] = Source.EndLine != 0 ? Source.EndLine : Source.Line;
  Result["end_column"] =
      Source.EndColumn != 0 ? Source.EndColumn : Source.Column;
  return Result;
}

static std::string leanProjectPath(llvm::StringRef Root,
                                   llvm::ArrayRef<llvm::StringRef> Components) {
  llvm::SmallString<256> Path(Root);
  for (llvm::StringRef Component : Components)
    llvm::sys::path::append(Path, Component);
  return std::string(Path);
}

static llvm::Error writeTextFile(llvm::StringRef Path,
                                 llvm::StringRef Contents) {
  std::error_code EC;
  llvm::raw_fd_ostream OS(Path, EC, llvm::sys::fs::OF_Text);
  if (EC)
    return llvm::createStringError(EC, "cannot write %s", Path.str().c_str());
  OS << Contents;
  OS.flush();
  if (OS.has_error())
    return llvm::createStringError(OS.error(), "cannot write %s",
                                   Path.str().c_str());
  return llvm::Error::success();
}

static llvm::Error writeTextFileIfMissing(llvm::StringRef Path,
                                          llvm::StringRef Contents) {
  if (llvm::sys::fs::exists(Path))
    return llvm::Error::success();
  return writeTextFile(Path, Contents);
}

static std::string leanGoalModuleName(llvm::StringRef Goal) {
  llvm::MD5 Hasher;
  llvm::MD5::MD5Result Hash;
  Hasher.update(Goal);
  Hasher.final(Hash);
  llvm::SmallString<32> Hex;
  llvm::MD5::stringifyResult(Hash, Hex);
  return "Goal_" + llvm::StringRef(Hex).take_front(16).str();
}

static llvm::Expected<std::string>
executeWithLogs(llvm::StringRef Program,
                const std::vector<std::string> &Arguments,
                llvm::StringRef LogBase) {
  std::vector<llvm::StringRef> ArgRefs;
  ArgRefs.reserve(Arguments.size());
  for (const std::string &Argument : Arguments)
    ArgRefs.push_back(Argument);
  const std::string StdoutPath = LogBase.str() + ".out";
  const std::string StderrPath = LogBase.str() + ".err";
  std::vector<std::optional<llvm::StringRef>> Redirects = {
      std::nullopt, StdoutPath, StderrPath};
  std::string ExecutionError;
  bool ExecutionFailed = false;
  const int ExitCode = llvm::sys::ExecuteAndWait(
      Program, ArgRefs, std::nullopt, Redirects, /*SecondsToWait=*/300,
      /*MemoryLimit=*/0, &ExecutionError, &ExecutionFailed);
  auto readLog = [](llvm::StringRef Path) {
    auto Buffer = llvm::MemoryBuffer::getFile(Path);
    return Buffer ? Buffer.get()->getBuffer().str() : std::string();
  };
  std::string Stdout = readLog(StdoutPath);
  std::string Stderr = readLog(StderrPath);
  llvm::sys::fs::remove(StdoutPath);
  llvm::sys::fs::remove(StderrPath);
  if (ExecutionFailed || ExitCode != 0) {
    std::string Message = ExecutionError;
    if (!Stdout.empty())
      Message += (Message.empty() ? "" : "\n") + Stdout;
    if (!Stderr.empty())
      Message += (Message.empty() ? "" : "\n") + Stderr;
    if (Message.size() > 4000)
      Message.resize(4000);
    return llvm::createStringError(llvm::inconvertibleErrorCode(),
                                   "command failed with exit code %d: %s",
                                   ExitCode, Message.c_str());
  }
  return Stdout;
}

class Verifier {
  ASTContext &Ctx;
  VerifyOptions Opts;
  llvm::raw_ostream *DumpOS = nullptr;
  std::vector<VerifyDiagnostic> Diags;

  const std::string &leanProjectRoot() const {
    return Opts.LeanProjectPath.empty() ? Opts.LeanFallbackProjectPath
                                        : Opts.LeanProjectPath;
  }

  llvm::Error emitObligationArchive(const ObligationModule &Module) {
    if (!Opts.ObligationOut)
      return llvm::Error::success();

    std::string Serialized = serializeObligationModule(Module);
    auto RoundTrip = deserializeObligationModules(Serialized);
    if (!RoundTrip)
      return RoundTrip.takeError();
    if (RoundTrip->size() != 1 ||
        serializeObligationModule(RoundTrip->front()) != Serialized ||
        obligationSemanticHash(RoundTrip->front()) !=
            obligationSemanticHash(Module))
      return llvm::createStringError(
          llvm::inconvertibleErrorCode(),
          "canonical obligation serialization did not round-trip");
    *Opts.ObligationOut << Serialized;
    return llvm::Error::success();
  }

  void annotateObligationSources(ObligationModule &Module) {
    const SourceManager &SourceMgr = Ctx.getSourceManager();
    auto annotateSource = [&](SourceLocation Loc, SourceLocation EndLoc,
                              ObligationSource &Source) {
      if (!Loc.isValid())
        return;
      PresumedLoc Location = SourceMgr.getPresumedLoc(Loc);
      if (!Location.isValid())
        return;
      Source.File = Location.getFilename();
      Source.Line = Location.getLine();
      Source.Column = Location.getColumn();
      PresumedLoc End =
          SourceMgr.getPresumedLoc(EndLoc.isValid() ? EndLoc : Loc);
      if (End.isValid() && Source.File == End.getFilename() &&
          (End.getLine() > Source.Line || (End.getLine() == Source.Line &&
                                           End.getColumn() >= Source.Column))) {
        Source.EndLine = End.getLine();
        Source.EndColumn = End.getColumn();
      } else {
        Source.EndLine = Source.Line;
        Source.EndColumn = Source.Column;
      }
    };
    auto annotateExpr = [&](LogicExpr *Root) {
      if (!Root)
        return;
      std::vector<LogicExpr *> Pending = {Root};
      while (!Pending.empty()) {
        LogicExpr *Expr = Pending.back();
        Pending.pop_back();
        annotateSource(Expr->Loc, Expr->EndLoc, Expr->Source);
        for (auto &Child : Expr->Children)
          if (Child)
            Pending.push_back(Child.get());
      }
    };

    annotateExpr(Module.CorrectnessGoal.get());
    annotateExpr(Module.CounterexampleQuery.get());
    std::map<std::string, unsigned> StableIdCounts;
    for (Obligation &Item : Module.Obligations) {
      annotateSource(Item.Loc, Item.EndLoc, Item.Source);
      const char *Kind = Item.Kind == ObligationKind::Postcondition
                             ? "postcondition"
                         : Item.Kind == ObligationKind::Unwinding ? "unwinding"
                                                                  : "assertion";
      std::string StableId = Module.FunctionIdentity + "::" + Kind + "@";
      StableId += Item.Source.isValid()
                      ? std::to_string(Item.Source.Line) + ":" +
                            std::to_string(Item.Source.Column)
                      : "synthetic";
      unsigned &Count = StableIdCounts[StableId];
      if (++Count > 1)
        StableId += "#" + std::to_string(Count);
      Item.StableId = std::move(StableId);
      annotateExpr(Item.Goal.get());
      annotateExpr(Item.CounterexampleQuery.get());
    }
    for (auto &[InternalName, Variable] : Module.DiagnosticVariables) {
      (void)InternalName;
      annotateSource(Variable.Loc, Variable.EndLoc, Variable.Source);
    }
    for (DiagnosticTraceEvent &Event : Module.TraceEvents) {
      annotateSource(Event.Loc, Event.EndLoc, Event.Source);
      annotateExpr(Event.Guard.get());
      for (DiagnosticTraceValue &Value : Event.Values)
        annotateExpr(Value.Value.get());
    }
    for (auto &[Identity, Function] : Module.LogicFunctions) {
      (void)Identity;
      annotateExpr(Function.StepDefinition.get());
      for (auto &Definition : Function.DefinitionLevels)
        annotateExpr(Definition.get());
    }
  }

  llvm::Expected<std::string> initializeLeanProject() {
    const std::string &Root = leanProjectRoot();
    std::error_code EC = llvm::sys::fs::create_directories(
        leanProjectPath(Root, {"CppVerify", "Proofs"}));
    if (EC)
      return llvm::createStringError(EC, "cannot create Lean project %s",
                                     Root.c_str());

    const std::string ToolchainPath = leanProjectPath(Root, {"lean-toolchain"});
    constexpr llvm::StringLiteral Toolchain = "leanprover/lean4:v4.32.2\n";
    if (llvm::sys::fs::exists(ToolchainPath)) {
      auto Existing = llvm::MemoryBuffer::getFile(ToolchainPath);
      if (!Existing)
        return llvm::createStringError(Existing.getError(),
                                       "cannot read Lean toolchain pin");
      if (Existing.get()->getBuffer().trim() !=
          llvm::StringRef(Toolchain).trim())
        return llvm::createStringError(
            llvm::inconvertibleErrorCode(),
            "Lean project uses toolchain '%s'; expected '%s'",
            Existing.get()->getBuffer().trim().str().c_str(),
            llvm::StringRef(Toolchain).trim().str().c_str());
    } else if (llvm::Error Error = writeTextFile(ToolchainPath, Toolchain)) {
      return std::move(Error);
    }

    constexpr llvm::StringLiteral Lakefile =
        "name = \"cppverify_proof\"\n"
        "version = \"0.1.0\"\n"
        "defaultTargets = [\"CppVerify\"]\n\n"
        "[[lean_lib]]\n"
        "name = \"CppVerify\"\n";
    if (llvm::Error Error = writeTextFileIfMissing(
            leanProjectPath(Root, {"lakefile.toml"}), Lakefile))
      return std::move(Error);

    constexpr llvm::StringLiteral UserFile =
        "import CppVerify.Generated\n\n"
        "/- Add reusable lemmas here. This file is never regenerated. -/\n";
    if (llvm::Error Error = writeTextFileIfMissing(
            leanProjectPath(Root, {"CppVerify", "User.lean"}), UserFile))
      return std::move(Error);

    return leanProjectPath(Root, {"CppVerify", "Generated.lean"});
  }

  llvm::Error
  finalizeLeanProject(const std::vector<std::string> &ProjectGoals) {
    const std::string &Root = leanProjectRoot();
    std::set<std::string> UniqueGoals(ProjectGoals.begin(), ProjectGoals.end());
    std::string CheckFile;
    for (const std::string &Goal : UniqueGoals) {
      const std::string Module = leanGoalModuleName(Goal);
      const std::string ProofPath =
          leanProjectPath(Root, {"CppVerify", "Proofs", Module + ".lean"});
      std::string Proof =
          "import CppVerify.User\n\n"
          "/- Complete this proof; this file is never regenerated. -/\n"
          "theorem " +
          Goal + "_proof : " + Goal + " := by\n  sorry\n";
      if (llvm::Error Error = writeTextFileIfMissing(ProofPath, Proof))
        return Error;
      CheckFile += "import CppVerify.Proofs." + Module + "\n";
    }
    CheckFile += "\n";
    for (const std::string &Goal : UniqueGoals) {
      CheckFile += "example : " + Goal + " := " + Goal + "_proof\n";
      CheckFile += "#print axioms " + Goal + "_proof\n";
    }
    return writeTextFile(leanProjectPath(Root, {"CppVerify", "Check.lean"}),
                         CheckFile);
  }

  llvm::Error certifyLeanProject(const std::vector<std::string> &ProjectGoals) {
    if (ProjectGoals.empty())
      return llvm::createStringError(llvm::inconvertibleErrorCode(),
                                     "the project has no proof obligations");
    auto Lake = llvm::sys::findProgramByName("lake");
    if (!Lake)
      return llvm::createStringError(Lake.getError(),
                                     "cannot find the Lean project launcher");

    const std::string &Root = leanProjectRoot();
    const std::string LogBase =
        leanProjectPath(Root, {".cppverify-certification"});
    auto runLake = [&](std::vector<std::string> Arguments,
                       llvm::StringRef Stage) -> llvm::Expected<std::string> {
      std::vector<std::string> Command = {"lake", "--dir=" + Root};
      Command.insert(Command.end(), std::make_move_iterator(Arguments.begin()),
                     std::make_move_iterator(Arguments.end()));
      return executeWithLogs(*Lake, Command, LogBase + "-" + Stage.str());
    };

    if (auto Build = runLake({"build", "CppVerify.Generated", "CppVerify.User"},
                             "build");
        !Build)
      return Build.takeError();

    const std::string UserObject = leanProjectPath(
        Root, {".lake", "build", "lib", "lean", "CppVerify", "User.olean"});
    if (auto User =
            runLake({"env", "lean", "-EhasSorry", "-R", Root, "-o", UserObject,
                     leanProjectPath(Root, {"CppVerify", "User.lean"})},
                    "user");
        !User)
      return User.takeError();

    const std::string ProofBuildDir = leanProjectPath(
        Root, {".lake", "build", "lib", "lean", "CppVerify", "Proofs"});
    if (std::error_code EC = llvm::sys::fs::create_directories(ProofBuildDir))
      return llvm::createStringError(
          EC, "cannot create Lean proof build directory");

    std::set<std::string> UniqueGoals(ProjectGoals.begin(), ProjectGoals.end());
    for (const std::string &Goal : UniqueGoals) {
      const std::string Module = leanGoalModuleName(Goal);
      const std::string ProofSource =
          leanProjectPath(Root, {"CppVerify", "Proofs", Module + ".lean"});
      const std::string ProofObject =
          leanProjectPath(ProofBuildDir, {Module + ".olean"});
      if (auto Proof = runLake({"env", "lean", "-EhasSorry", "-R", Root, "-o",
                                ProofObject, ProofSource},
                               Module);
          !Proof)
        return Proof.takeError();
    }

    auto Check = runLake({"env", "lean", "-R", Root,
                          leanProjectPath(Root, {"CppVerify", "Check.lean"})},
                         "check");
    if (!Check)
      return Check.takeError();

    const std::set<llvm::StringRef> AllowedAxioms = {"propext", "Quot.sound",
                                                     "Classical.choice"};
    unsigned Reports = 0;
    llvm::StringRef Report = *Check;
    llvm::StringRef NoAxioms = "does not depend on any axioms";
    for (size_t Pos = Report.find(NoAxioms); Pos != llvm::StringRef::npos;
         Pos = Report.find(NoAxioms, Pos + NoAxioms.size()))
      ++Reports;
    llvm::StringRef HasAxioms = "depends on axioms:";
    for (size_t Pos = Report.find(HasAxioms); Pos != llvm::StringRef::npos;
         Pos = Report.find(HasAxioms, Pos + HasAxioms.size())) {
      ++Reports;
      const size_t Open = Report.find('[', Pos + HasAxioms.size());
      const size_t Close = Open == llvm::StringRef::npos
                               ? llvm::StringRef::npos
                               : Report.find(']', Open + 1);
      if (Open == llvm::StringRef::npos || Close == llvm::StringRef::npos)
        return llvm::createStringError(
            llvm::inconvertibleErrorCode(),
            "malformed Lean axiom-dependency report");
      llvm::SmallVector<llvm::StringRef> Axioms;
      Report.slice(Open + 1, Close).split(Axioms, ',', -1, false);
      for (llvm::StringRef Axiom : Axioms) {
        Axiom = Axiom.trim();
        if (!Axiom.empty() && !AllowedAxioms.count(Axiom))
          return llvm::createStringError(
              llvm::inconvertibleErrorCode(),
              "proof depends on undocumented axiom %s", Axiom.str().c_str());
      }
    }
    if (Reports != UniqueGoals.size())
      return llvm::createStringError(
          llvm::inconvertibleErrorCode(),
          "Lean did not report axiom dependencies for every proof");
    return llvm::Error::success();
  }

  void checkCalleeRecommendsOnFailure(const VFunction &Caller,
                                      const FunctionMap &FnMap,
                                      VerifyBackend &Backend) {
    std::vector<const VSpecCallExpr *> Calls;
    collectSpecCallsInFunction(Caller, Calls);
    for (const VSpecCallExpr *C : Calls) {
      auto It = FnMap.find(C->CalleeIdentity);
      if (It == FnMap.end() || It->second->Recommends.empty())
        continue;
      std::map<std::string, std::unique_ptr<VExpr>> ArgMap;
      for (unsigned I = 0; I < It->second->Params.size() && I < C->Args.size();
           ++I)
        ArgMap[It->second->Params[I].first] = cloneVExpr(C->Args[I].get());
      PassiveProgram PP;
      PP.FunctionName = Caller.Name + ".recommends";
      PP.FunctionIdentity =
          Caller.Identity + "::recommends::" + C->CalleeIdentity;
      for (const auto &Pre : Caller.Preconditions)
        PP.EntryAssumes.push_back(cloneVExpr(Pre.get()));
      for (const auto &Rec : It->second->Recommends) {
        auto Inst = substParamsInExpr(Rec.get(), ArgMap);
        if (!Inst)
          continue;
        Inst = SpecInliner(FnMap, Caller.SpecFuel).inlineExpr(std::move(Inst));
        PP.ExitAsserts.push_back(std::move(Inst));
      }
      if (PP.ExitAsserts.empty())
        continue;
      PP.CallerIntMode = Caller.IntMode;
      auto Module = buildObligationModule(PP);
      if (!Module) {
        Diags.push_back({VerifyDiagnostic::Unresolved,
                         "recommends lowering failed for " + Caller.Name +
                             " (" + llvm::toString(Module.takeError()) + ")"});
        continue;
      }
      annotateObligationSources(*Module);
      VerifyResult R = Backend.verify(*Module);
      if (R.Status == VerifyStatus::Failed)
        Diags.push_back({VerifyDiagnostic::Warning,
                         "recommends of spec " + C->Callee +
                             " may be violated at call in " + Caller.Name});
    }
  }

public:
  Verifier(ASTContext &Ctx, const VerifyOptions &Opts,
           llvm::raw_ostream &DumpOS)
      : Ctx(Ctx), Opts(Opts), DumpOS(&DumpOS) {}

  bool run() {
    if (!Opts.LeanOutPath.empty() && Opts.Backend != BackendKind::Lean) {
      Diags.push_back(
          {VerifyDiagnostic::Error, "--lean-out requires --backend=lean"});
      return false;
    }
    if (!Opts.LeanProjectPath.empty() && Opts.Backend != BackendKind::Lean) {
      Diags.push_back(
          {VerifyDiagnostic::Error, "--lean-project requires --backend=lean"});
      return false;
    }
    if (!Opts.LeanFallbackProjectPath.empty() &&
        Opts.Backend != BackendKind::Z3 &&
        Opts.Backend != BackendKind::Portfolio) {
      Diags.push_back(
          {VerifyDiagnostic::Error,
           "--lean-fallback requires --backend=z3 or --backend=portfolio"});
      return false;
    }
    if (!Opts.LeanFallbackProjectPath.empty() &&
        (!Opts.LeanProjectPath.empty() || !Opts.LeanOutPath.empty())) {
      Diags.push_back(
          {VerifyDiagnostic::Error,
           "--lean-fallback is mutually exclusive with --lean-project and "
           "--lean-out"});
      return false;
    }
    if (!Opts.LeanFallbackProjectPath.empty() && Opts.LowerOnly) {
      Diags.push_back({VerifyDiagnostic::Error,
                       "--lean-fallback cannot be combined with --lower-only"});
      return false;
    }
    if (!Opts.LeanProjectPath.empty() && !Opts.LeanOutPath.empty()) {
      Diags.push_back({VerifyDiagnostic::Error,
                       "--lean-project and --lean-out are mutually exclusive"});
      return false;
    }
    if (Opts.LeanCertify && Opts.LeanProjectPath.empty() &&
        Opts.LeanFallbackProjectPath.empty()) {
      Diags.push_back({VerifyDiagnostic::Error,
                       "--lean-certify requires --lean-project or "
                       "--lean-fallback"});
      return false;
    }
    if (Opts.LowerOnly && Opts.Backend == BackendKind::Lean) {
      Diags.push_back(
          {VerifyDiagnostic::Error,
           "--lower-only supports Z3, cvc5, portfolio, and BMC; use "
           "--backend=lean to validate Lean export"});
      return false;
    }
    if (Opts.Backend == BackendKind::Lean &&
        (Opts.Jobs != 1 || !Opts.ProofCachePath.empty())) {
      Diags.push_back(
          {VerifyDiagnostic::Error,
           "--jobs and --proof-cache are not supported by the Lean backend"});
      return false;
    }
    if (Opts.Backend == BackendKind::CVC5 && !Opts.ProofCachePath.empty()) {
      Diags.push_back({VerifyDiagnostic::Error,
                       "--proof-cache is not supported by --backend=cvc5; use "
                       "--backend=portfolio to cache its Z3 component"});
      return false;
    }
    if (!Opts.CVC5Path.empty() && Opts.Backend != BackendKind::CVC5 &&
        Opts.Backend != BackendKind::Portfolio) {
      Diags.push_back(
          {VerifyDiagnostic::Error,
           "--cvc5-path requires --backend=cvc5 or --backend=portfolio"});
      return false;
    }
    if (Opts.LowerOnly && !Opts.ProofCachePath.empty()) {
      Diags.push_back({VerifyDiagnostic::Error,
                       "--proof-cache cannot be combined with --lower-only"});
      return false;
    }

    ASTConverter DiscoveryConverter(Ctx);
    auto DiscoveryFunctions = DiscoveryConverter.convertTranslationUnit();
    inferFreshOwnedReturns(DiscoveryFunctions);
    std::set<std::string> FreshOwnedCalleeIdentities;
    for (const auto &Fn : DiscoveryFunctions)
      if (Fn->FreshOwnedReturn)
        FreshOwnedCalleeIdentities.insert(Fn->Identity);

    ASTConverter Converter(Ctx, FreshOwnedCalleeIdentities);
    auto Functions = Converter.convertTranslationUnit();
    for (const std::string &Err : Converter.getErrors())
      Diags.push_back({VerifyDiagnostic::Error, Err});
    if (!Converter.getErrors().empty())
      return false;
    if (Functions.empty()) {
      if (Opts.LeanCertify) {
        Diags.push_back({VerifyDiagnostic::Unresolved,
                         "Lean certification requires at least one proof "
                         "obligation"});
        return false;
      }
      Diags.push_back(
          {VerifyDiagnostic::Warning, "no verifiable functions found"});
      return true;
    }
    inferFreshOwnedReturns(Functions);

    FunctionMap FnMap;
    for (const auto &Fn : Functions)
      FnMap[Fn->Identity] = Fn.get();

    std::vector<std::unique_ptr<VFunction>> InterfaceFunctions;
    FunctionMap InterfaceMap;
    InterfaceFunctions.reserve(Functions.size());
    for (const auto &Fn : Functions) {
      auto Interface = std::make_unique<VFunction>(cloneVFunction(*Fn));
      if (!Interface->IsSpec && Opts.CheckUB &&
          (isDeductiveBackend(Opts.Backend) ||
           Opts.Backend == BackendKind::BMC ||
           Opts.Backend == BackendKind::Lean))
        (void)instrumentUBChecks(*Interface);
      InterfaceMap[Interface->Identity] = Interface.get();
      InterfaceFunctions.push_back(std::move(Interface));
    }

    std::vector<std::string> LeanProjectGoals;
    std::unique_ptr<llvm::raw_fd_ostream> LeanFile;
    llvm::raw_ostream *LeanOut = DumpOS;
    std::string LeanOutputPath = Opts.LeanOutPath;
    const bool HasLeanProject =
        !Opts.LeanProjectPath.empty() || !Opts.LeanFallbackProjectPath.empty();
    if (HasLeanProject) {
      auto GeneratedPath = initializeLeanProject();
      if (!GeneratedPath) {
        Diags.push_back({VerifyDiagnostic::Error,
                         "cannot initialize Lean project (" +
                             llvm::toString(GeneratedPath.takeError()) + ")"});
        return false;
      }
      LeanOutputPath = std::move(*GeneratedPath);
    }
    if ((Opts.Backend == BackendKind::Lean ||
         !Opts.LeanFallbackProjectPath.empty()) &&
        !LeanOutputPath.empty()) {
      std::error_code EC;
      LeanFile = std::make_unique<llvm::raw_fd_ostream>(LeanOutputPath, EC,
                                                        llvm::sys::fs::OF_Text);
      if (EC) {
        Diags.push_back({VerifyDiagnostic::Error,
                         "cannot open lean output: " + LeanOutputPath});
        return false;
      }
      LeanOut = LeanFile.get();
    }

    BackendExecutionOptions Execution;
    Execution.SolverTimeoutMs = Opts.SolverTimeoutMs;
    Execution.SolverResourceLimit = Opts.SolverResourceLimit;
    Execution.Jobs = Opts.Jobs;
    Execution.MaxQueryNodes = Opts.MaxQueryNodes;
    Execution.SkipWholeModuleRetry = !Opts.LeanFallbackProjectPath.empty();
    Execution.CVC5Path = Opts.CVC5Path;
    Execution.ProofCachePath = Opts.ProofCachePath;
    Execution.ProofCacheMaxBytes = Opts.ProofCacheMaxBytes;
    Execution.ProofCacheMaxEntries = Opts.ProofCacheMaxEntries;
    auto Backend = createVerifyBackend(
        Opts.Backend, LeanOut, Opts.BMCUnroll, Execution,
        Opts.LeanProjectPath.empty() ? nullptr : &LeanProjectGoals);
    std::unique_ptr<VerifyBackend> LeanFallbackBackend;
    if (!Opts.LeanFallbackProjectPath.empty())
      LeanFallbackBackend = createVerifyBackend(
          BackendKind::Lean, LeanFile.get(), 0, {}, &LeanProjectGoals);
    Passivizer P;
    P.setFunctionMap(InterfaceMap);

    const unsigned DumpLayers = Opts.DumpIRLayers;
    const bool MultiLayerDump = llvm::popcount(DumpLayers) > 1;
    bool AllOk = true;
    bool AnyFailed = false;
    std::set<std::string> FailedCallers;
    auto exportLeanFallback = [&](const ObligationModule &Module,
                                  llvm::StringRef Label) {
      if (!LeanFallbackBackend)
        return false;
      VerifyResult Fallback = LeanFallbackBackend->verify(Module);
      if (Fallback.Status == VerifyStatus::Exported) {
        Diags.push_back({VerifyDiagnostic::Exported,
                         "lean fallback: " + Label.str(), Fallback.Location,
                         Label.str(), std::move(Fallback)});
        return true;
      }
      std::string Message = "lean fallback export failed: " + Label.str();
      if (!Fallback.Message.empty())
        Message += " (" + Fallback.Message + ")";
      Diags.push_back({VerifyDiagnostic::Unresolved, std::move(Message),
                       Fallback.Location, Label.str(), std::move(Fallback)});
      return false;
    };

    for (const auto &Fn : Functions) {
      if (Fn->IsExternalContract) {
        Diags.push_back({VerifyDiagnostic::Warning,
                         "assuming external contract: " + Fn->Name});
        continue;
      }
      bool DumpedAny = false;
      auto dumpSep = [&]() {
        if (DumpedAny && MultiLayerDump)
          *DumpOS << "======\n";
        DumpedAny = true;
      };

      std::optional<VFunction> PreparedFn;
      std::optional<VFunction> UnrolledFn;
      std::optional<std::string> UBError;
      const VFunction *WorkFn = Fn.get();
      if (!Fn->IsSpec) {
        PreparedFn = cloneVFunction(*Fn);
        // `valid(p, n)` is a recognized UB marker. Discover it before spec
        // preparation folds its deliberately trivial body to `true`.
        if (Opts.CheckUB && (isDeductiveBackend(Opts.Backend) ||
                             Opts.Backend == BackendKind::BMC ||
                             Opts.Backend == BackendKind::Lean))
          UBError = instrumentUBChecks(*PreparedFn);
        if (!UBError) {
          SpecInliner Inliner(FnMap, PreparedFn->SpecFuel);
          if (isDeductiveBackend(Opts.Backend) ||
              Opts.Backend == BackendKind::Lean)
            Inliner.prepareFunctionAxiomatic(*PreparedFn);
          else
            Inliner.prepareFunction(*PreparedFn);
        }
        WorkFn = &*PreparedFn;
        if (!UBError && Opts.Backend == BackendKind::BMC && Opts.LowerOnly) {
          UnrolledFn = LoopUnroller::unroll(*PreparedFn, Opts.BMCUnroll);
          WorkFn = &*UnrolledFn;
        }
      }

      if (UBError) {
        AllOk = false;
        AnyFailed = true;
        if (!Fn->IsProof)
          FailedCallers.insert(Fn->Identity);
        Diags.push_back({VerifyDiagnostic::Error, Fn->Name + ": " + *UBError});
        continue;
      }

      if (Fn->IsSpec && !Fn->NeedsDecreasesCheck) {
        const VerifyDiagnostic::Kind Kind =
            Opts.LowerOnly ? VerifyDiagnostic::Lowered
                           : (Opts.Backend == BackendKind::Lean
                                  ? VerifyDiagnostic::Exported
                                  : VerifyDiagnostic::Verified);
        if (Fn->IsConstexprSpec)
          Diags.push_back({Kind, "constexpr spec axiom: " + Fn->Name});
        else
          Diags.push_back({Kind, "spec axiom: " + Fn->Name});
        continue;
      }

      if (Fn->NeedsDecreasesCheck) {
        PassiveProgram DecPP = buildDecreasesChecks(*Fn, FnMap);
        auto DecModuleOrErr = buildObligationModule(DecPP);
        if (!DecModuleOrErr) {
          AllOk = false;
          AnyFailed = true;
          Diags.push_back(
              {VerifyDiagnostic::Unresolved,
               "obligation lowering failed for decreases: " + Fn->Name + " (" +
                   llvm::toString(DecModuleOrErr.takeError()) + ")"});
          continue;
        }
        ObligationSimplificationStats DecSimplification;
        auto SimplifiedDecModule = simplifyObligationModule(
            std::move(*DecModuleOrErr), &DecSimplification);
        if (!SimplifiedDecModule) {
          AllOk = false;
          AnyFailed = true;
          Diags.push_back(
              {VerifyDiagnostic::Unresolved,
               "obligation simplification failed for decreases: " + Fn->Name +
                   " (" + llvm::toString(SimplifiedDecModule.takeError()) +
                   ")"});
          continue;
        }
        ObligationModule DecModule = std::move(*SimplifiedDecModule);
        if (Opts.Backend == BackendKind::BMC)
          DecModule.BMCTransform = BMCTransformProvenance{Opts.BMCUnroll};
        annotateObligationSources(DecModule);
        if (llvm::Error Error = emitObligationArchive(DecModule)) {
          AllOk = false;
          AnyFailed = true;
          Diags.push_back(
              {VerifyDiagnostic::Error,
               "cannot serialize decreases obligation: " + Fn->Name + " (" +
                   llvm::toString(std::move(Error)) + ")"});
          continue;
        }
        if (Opts.LowerOnly) {
          VerifyResult DR = lowerForBackend(DecModule, Opts.Backend, Execution);
          if (DR.Status != VerifyStatus::Lowered) {
            AllOk = false;
            AnyFailed = true;
            std::string Message =
                std::string(Opts.Backend == BackendKind::Z3 ||
                                    Opts.Backend == BackendKind::BMC
                                ? "Z3"
                                : "backend") +
                " lowering failed for decreases: " + Fn->Name;
            Message += backendSuffix(DR);
            if (!DR.Message.empty())
              Message += " (" + DR.Message + ")";
            Diags.push_back({VerifyDiagnostic::Error, std::move(Message),
                             DR.Location, Fn->Name, std::move(DR)});
            continue;
          }
          if (Fn->IsSpec) {
            Diags.push_back({VerifyDiagnostic::Lowered,
                             "spec decreases: " + Fn->Name, SourceLocation(),
                             Fn->Name, DR});
            continue;
          }
        } else {
          VerifyResult R = Backend->verify(DecModule);
          if (R.Status == VerifyStatus::Exported) {
            Diags.push_back({VerifyDiagnostic::Exported,
                             "decreases: " + Fn->Name, R.Location, Fn->Name,
                             R});
            if (Fn->IsSpec)
              continue;
          } else if (R.Status == VerifyStatus::Verified) {
            if (Fn->IsSpec) {
              Diags.push_back({VerifyDiagnostic::Verified,
                               "spec decreases: " + Fn->Name, R.Location,
                               Fn->Name, R});
              continue;
            }
          } else {
            const bool IsUnresolved = R.Status == VerifyStatus::Unresolved;
            const bool FallbackExported =
                IsUnresolved &&
                exportLeanFallback(DecModule, "decreases: " + Fn->Name);
            if (Opts.LeanCertify && FallbackExported) {
              if (Fn->IsSpec)
                continue;
            } else {
              AllOk = false;
              AnyFailed = true;
              if (!Fn->IsProof)
                FailedCallers.insert(Fn->Identity);
              std::string Message =
                  std::string(Fn->IsSpec ? "spec decreases " : "decreases ") +
                  (IsUnresolved ? "unresolved: " : "failed: ") + Fn->Name +
                  backendSuffix(R);
              if (!R.Message.empty())
                Message += " (" + R.Message + ")";
              Diags.push_back({IsUnresolved ? VerifyDiagnostic::Unresolved
                                            : VerifyDiagnostic::Error,
                               std::move(Message), R.Location, Fn->Name, R});
              continue;
            }
          }
        }
      }

      std::optional<PassiveProgram> BMCProgram;
      std::optional<ObligationModule> BMCModule;
      std::optional<VerifyResult> BMCResult;
      ObligationSimplificationStats BMCSimplification;
      if (Opts.Backend == BackendKind::BMC && !Opts.LowerOnly) {
        std::vector<unsigned> ExploredBounds;
        uint64_t CacheHits = 0;
        uint64_t CacheMisses = 0;
        uint64_t CacheErrors = 0;
        uint64_t ReusedQueries = 0;
        std::string CacheError;
        bool PreparationFailed = false;
        for (unsigned Bound = 0;; ++Bound) {
          UnrolledFn = LoopUnroller::unroll(*PreparedFn, Bound);
          Passivizer BoundPassivizer;
          BoundPassivizer.setFunctionMap(InterfaceMap);
          PassiveProgram BoundProgram = BoundPassivizer.run(*UnrolledFn);
          auto BoundModuleOrErr = buildObligationModule(BoundProgram);
          if (!BoundModuleOrErr) {
            AllOk = false;
            AnyFailed = true;
            Diags.push_back(
                {VerifyDiagnostic::Unresolved,
                 "BMC obligation lowering failed at bound " +
                     std::to_string(Bound) + ": " + Fn->Name + " (" +
                     llvm::toString(BoundModuleOrErr.takeError()) + ")"});
            PreparationFailed = true;
            break;
          }
          ObligationSimplificationStats BoundSimplification;
          auto SimplifiedBoundModule = simplifyObligationModule(
              std::move(*BoundModuleOrErr), &BoundSimplification);
          if (!SimplifiedBoundModule) {
            AllOk = false;
            AnyFailed = true;
            Diags.push_back(
                {VerifyDiagnostic::Unresolved,
                 "BMC obligation simplification failed at bound " +
                     std::to_string(Bound) + ": " + Fn->Name + " (" +
                     llvm::toString(SimplifiedBoundModule.takeError()) + ")"});
            PreparationFailed = true;
            break;
          }
          ObligationModule BoundModule = std::move(*SimplifiedBoundModule);
          BoundModule.BMCTransform = BMCTransformProvenance{Bound};
          annotateObligationSources(BoundModule);
          VerifyResult Result = Backend->verify(BoundModule);
          ExploredBounds.push_back(Bound);
          CacheHits += Result.CacheHits;
          CacheMisses += Result.CacheMisses;
          CacheErrors += Result.CacheErrors;
          ReusedQueries += Result.ReusedQueries;
          if (CacheError.empty() && !Result.CacheError.empty())
            CacheError = Result.CacheError;

          if (Result.Status != VerifyStatus::BoundedSafe ||
              Bound == Opts.BMCUnroll) {
            Result.CacheHits = CacheHits;
            Result.CacheMisses = CacheMisses;
            Result.CacheErrors = CacheErrors;
            Result.CacheError = std::move(CacheError);
            Result.ReusedQueries = ReusedQueries;
            Result.ExploredBounds = std::move(ExploredBounds);
            WorkFn = &*UnrolledFn;
            BMCProgram = std::move(BoundProgram);
            BMCModule = std::move(BoundModule);
            BMCResult = std::move(Result);
            BMCSimplification = BoundSimplification;
            break;
          }
        }
        if (PreparationFailed)
          continue;
      }

      if (DumpLayers & LayerVCR) {
        dumpSep();
        dumpVFunction(*WorkFn, *DumpOS);
      }

      PassiveProgram PP = BMCProgram ? std::move(*BMCProgram) : P.run(*WorkFn);
      if (DumpLayers & LayerPassive) {
        dumpSep();
        dumpPassiveProgram(Fn->Name, PP, *DumpOS);
      }

      ObligationSimplificationStats Simplification;
      ObligationModule Module;
      if (BMCModule) {
        Module = std::move(*BMCModule);
        Simplification = BMCSimplification;
      } else {
        auto ModuleOrErr = buildObligationModule(PP);
        if (!ModuleOrErr) {
          AllOk = false;
          AnyFailed = true;
          Diags.push_back({VerifyDiagnostic::Unresolved,
                           "obligation lowering failed: " + Fn->Name + " (" +
                               llvm::toString(ModuleOrErr.takeError()) + ")"});
          continue;
        }
        auto SimplifiedModule =
            simplifyObligationModule(std::move(*ModuleOrErr), &Simplification);
        if (!SimplifiedModule) {
          AllOk = false;
          AnyFailed = true;
          Diags.push_back(
              {VerifyDiagnostic::Unresolved,
               "obligation simplification failed: " + Fn->Name + " (" +
                   llvm::toString(SimplifiedModule.takeError()) + ")"});
          continue;
        }
        Module = std::move(*SimplifiedModule);
        if (Opts.Backend == BackendKind::BMC)
          Module.BMCTransform = BMCTransformProvenance{Opts.BMCUnroll};
        annotateObligationSources(Module);
      }
      if (llvm::Error Error = emitObligationArchive(Module)) {
        AllOk = false;
        AnyFailed = true;
        Diags.push_back({VerifyDiagnostic::Error,
                         "cannot serialize obligation: " + Fn->Name + " (" +
                             llvm::toString(std::move(Error)) + ")"});
        continue;
      }

      if (DumpLayers & LayerVC) {
        dumpSep();
        dumpVC(Module, *DumpOS, &Simplification);
      }

      if (DumpLayers & LayerZ3) {
        if (DumpLayers & LayerZ3)
          dumpSep();
        VerifyResult Lowered = lowerObligationModule(Module, DumpOS, Execution);
        if (Lowered.Status != VerifyStatus::Lowered) {
          AllOk = false;
          AnyFailed = true;
          std::string Message = "Z3 lowering failed: " + Fn->Name;
          Message += backendSuffix(Lowered);
          if (!Lowered.Message.empty())
            Message += " (" + Lowered.Message + ")";
          Diags.push_back({VerifyDiagnostic::Error, std::move(Message),
                           Lowered.Location, Fn->Name, std::move(Lowered)});
          continue;
        }
      }
      if (Opts.LowerOnly) {
        VerifyResult Lowered = lowerForBackend(Module, Opts.Backend, Execution);
        if (Lowered.Status != VerifyStatus::Lowered) {
          AllOk = false;
          AnyFailed = true;
          std::string Message =
              std::string(Opts.Backend == BackendKind::Z3 ||
                                  Opts.Backend == BackendKind::BMC
                              ? "Z3"
                              : "backend") +
              " lowering failed: " + Fn->Name;
          Message += backendSuffix(Lowered);
          if (!Lowered.Message.empty())
            Message += " (" + Lowered.Message + ")";
          Diags.push_back({VerifyDiagnostic::Error, std::move(Message),
                           Lowered.Location, Fn->Name, std::move(Lowered)});
          continue;
        }
      }
      if (DumpLayers)
        DumpOS->flush();

      if (Opts.LowerOnly) {
        VerifyResult Result;
        Result.Status = VerifyStatus::Lowered;
        Result.BackendName =
            Opts.Backend == BackendKind::CVC5
                ? "cvc5"
                : (Opts.Backend == BackendKind::Portfolio ? "portfolio" : "z3");
        Diags.push_back({VerifyDiagnostic::Lowered, Fn->Name, SourceLocation(),
                         Fn->Name, std::move(Result)});
        continue;
      }

      VerifyResult R =
          BMCResult ? std::move(*BMCResult) : Backend->verify(Module);
      if (R.Status == VerifyStatus::Verified) {
        Diags.push_back({VerifyDiagnostic::Verified,
                         Fn->Name + backendSuffix(R), R.Location, Fn->Name, R});
      } else if (R.Status == VerifyStatus::Certified) {
        Diags.push_back({VerifyDiagnostic::Certified,
                         Fn->Name + backendSuffix(R), R.Location, Fn->Name, R});
      } else if (R.Status == VerifyStatus::Exported) {
        Diags.push_back({VerifyDiagnostic::Exported,
                         "lean obligation: " + Fn->Name, R.Location, Fn->Name,
                         R});
      } else if (R.Status == VerifyStatus::BoundedSafe) {
        AllOk = false;
        std::string Message = Fn->Name + backendSuffix(R);
        if (!R.Message.empty())
          Message += " (" + R.Message + ")";
        Diags.push_back({VerifyDiagnostic::BoundedSafe, std::move(Message),
                         R.Location, Fn->Name, R});
      } else if (R.Status == VerifyStatus::Failed) {
        AllOk = false;
        AnyFailed = true;
        if (!Fn->IsProof)
          FailedCallers.insert(Fn->Identity);
        std::string Msg = "verification failed: " + Fn->Name;
        if (!R.ObligationId.empty())
          Msg += " [" + R.ObligationId + "]";
        if (!R.Message.empty())
          Msg += " (counterexample: " + R.Message + ")";
        Msg += backendSuffix(R);
        Diags.push_back(
            {VerifyDiagnostic::Error, Msg, R.Location, Fn->Name, R});
      } else {
        const bool FallbackExported = R.Status == VerifyStatus::Unresolved &&
                                      exportLeanFallback(Module, Fn->Name);
        if (!(Opts.LeanCertify && FallbackExported)) {
          AllOk = false;
          AnyFailed = true;
          if (!Fn->IsProof)
            FailedCallers.insert(Fn->Identity);
          std::string Message = Fn->Name + backendSuffix(R);
          if (!R.Message.empty())
            Message += " (" + R.Message + ")";
          Diags.push_back({VerifyDiagnostic::Unresolved, std::move(Message),
                           R.Location, Fn->Name, R});
        }
      }
    }

    if (HasLeanProject) {
      if (LeanFile) {
        LeanFile->flush();
        LeanFile.reset();
      }
      if (llvm::Error Error = finalizeLeanProject(LeanProjectGoals)) {
        AllOk = false;
        AnyFailed = true;
        Diags.push_back({VerifyDiagnostic::Error,
                         "cannot finalize Lean project (" +
                             llvm::toString(std::move(Error)) + ")"});
      } else if (Opts.LeanCertify && !AnyFailed &&
                 (!LeanProjectGoals.empty() ||
                  Opts.LeanFallbackProjectPath.empty())) {
        if (llvm::Error Error = certifyLeanProject(LeanProjectGoals)) {
          AllOk = false;
          AnyFailed = true;
          const std::string Reason = llvm::toString(std::move(Error));
          for (VerifyDiagnostic &Diagnostic : Diags) {
            if (Diagnostic.K != VerifyDiagnostic::Exported)
              continue;
            Diagnostic.K = VerifyDiagnostic::Unresolved;
            Diagnostic.Message +=
                " (Lean certification failed: " + Reason + ")";
            if (Diagnostic.Result) {
              Diagnostic.Result->Status = VerifyStatus::Unresolved;
              Diagnostic.Result->Reason = VerifyReason::LeanExportFailure;
              Diagnostic.Result->Message = Reason;
            }
          }
        } else {
          for (VerifyDiagnostic &Diagnostic : Diags) {
            if (Diagnostic.K != VerifyDiagnostic::Exported)
              continue;
            Diagnostic.K = VerifyDiagnostic::Certified;
            llvm::StringRef Name = Diagnostic.Message;
            if (!Name.consume_front("lean obligation: "))
              Name.consume_front("lean fallback: ");
            Diagnostic.Message = Name.str() + " [backend=Lean]";
            if (Diagnostic.Result) {
              Diagnostic.Result->Status = VerifyStatus::Certified;
              Diagnostic.Result->BackendName = "lean";
              Diagnostic.Result->Reason = VerifyReason::None;
            }
          }
        }
      }
    }

    if (AnyFailed && !Opts.LowerOnly && isDeductiveBackend(Opts.Backend)) {
      BackendExecutionOptions RecommendsExecution = Execution;
      RecommendsExecution.Jobs = 1;
      RecommendsExecution.ProofCachePath.clear();
      auto Z3 =
          createVerifyBackend(BackendKind::Z3, nullptr, 0, RecommendsExecution);
      for (const auto &Fn : Functions) {
        if (!FailedCallers.count(Fn->Identity) || Fn->IsSpec || Fn->IsProof ||
            Fn->IsExternalContract)
          continue;
        checkCalleeRecommendsOnFailure(*Fn, FnMap, *Z3);
      }
    }

    return AllOk;
  }

  void printJSONDiagnostic(const VerifyDiagnostic &D,
                           llvm::raw_ostream &OS) const {
    llvm::json::Object Record;
    Record["schema"] = "cppverify.diagnostic/1";
    Record["status"] =
        D.Result ? verifyStatusCode(D.Result->Status) : diagnosticKindCode(D.K);
    Record["severity"] =
        D.K == VerifyDiagnostic::Warning || D.K == VerifyDiagnostic::BoundedSafe
            ? "warning"
        : D.K == VerifyDiagnostic::Error || D.K == VerifyDiagnostic::Unresolved
            ? "error"
            : "note";
    Record["message"] = jsonText(D.Message);
    if (!D.FunctionName.empty())
      Record["function"] = jsonText(D.FunctionName);

    ObligationSource Source;
    if (D.Result)
      Source = D.Result->Source;
    if (!Source.isValid() && D.Loc.isValid()) {
      PresumedLoc Location = Ctx.getSourceManager().getPresumedLoc(D.Loc);
      if (Location.isValid()) {
        Source.File = Location.getFilename();
        Source.Line = Location.getLine();
        Source.Column = Location.getColumn();
        Source.EndLine = Source.Line;
        Source.EndColumn = Source.Column;
      }
    }
    if (Source.isValid())
      Record["source"] = sourceJSON(Source);

    if (D.Result) {
      const VerifyResult &Result = *D.Result;
      if (!Result.BackendName.empty())
        Record["backend"] = Result.BackendName;
      if (Result.Reason != VerifyReason::None)
        Record["reason"] = verifyReasonCode(Result.Reason);
      if (Result.Bound)
        Record["bound"] = static_cast<int64_t>(*Result.Bound);
      if (!Result.ExploredBounds.empty()) {
        llvm::json::Array Bounds;
        for (unsigned Bound : Result.ExploredBounds)
          Bounds.push_back(static_cast<int64_t>(Bound));
        Record["explored_bounds"] = std::move(Bounds);
      }
      if (Result.ReusedQueries)
        Record["reused_queries"] = static_cast<int64_t>(Result.ReusedQueries);
      if (Result.CacheHits || Result.CacheMisses || Result.CacheErrors) {
        llvm::json::Object Cache;
        Cache["hits"] = static_cast<int64_t>(Result.CacheHits);
        Cache["misses"] = static_cast<int64_t>(Result.CacheMisses);
        Cache["errors"] = static_cast<int64_t>(Result.CacheErrors);
        Record["cache"] = std::move(Cache);
      }
      if (!Result.CacheError.empty())
        Record["cache_error"] = jsonText(Result.CacheError);
      if (!Result.ObligationId.empty()) {
        llvm::json::Object Obligation;
        Obligation["id"] = jsonText(Result.ObligationId);
        if (Result.ObligationType)
          Obligation["kind"] = obligationKindCode(*Result.ObligationType);
        if (Result.Source.isValid())
          Obligation["source"] = sourceJSON(Result.Source);
        Record["obligation"] = std::move(Obligation);
      }
      if (!Result.Model.empty()) {
        llvm::json::Array Model;
        for (const VerifyModelValue &Value : Result.Model) {
          llvm::json::Object Entry;
          Entry["name"] = jsonText(Value.DisplayName);
          Entry["ssa_name"] = jsonText(Value.InternalName);
          Entry["sort"] = formatLogicSort(Value.Sort);
          Entry["value"] = Value.Value
                               ? llvm::json::Value(jsonText(*Value.Value))
                               : llvm::json::Value(nullptr);
          if (Value.Source.isValid())
            Entry["source"] = sourceJSON(Value.Source);
          Model.push_back(std::move(Entry));
        }
        Record["model"] = std::move(Model);
      }
      if (!Result.Trace.empty()) {
        llvm::json::Array Trace;
        for (const VerifyTraceEvent &Event : Result.Trace) {
          llvm::json::Object Entry;
          Entry["kind"] = traceKindCode(Event.Kind);
          Entry["message"] = jsonText(Event.Message);
          Entry["active"] = Event.Active ? llvm::json::Value(*Event.Active)
                                         : llvm::json::Value(nullptr);
          if (Event.Source.isValid())
            Entry["source"] = sourceJSON(Event.Source);
          llvm::json::Array Values;
          for (const VerifyTraceValue &Value : Event.Values) {
            llvm::json::Object Item;
            Item["label"] = jsonText(Value.Label);
            Item["sort"] = formatLogicSort(Value.Sort);
            Item["value"] = Value.Value
                                ? llvm::json::Value(jsonText(*Value.Value))
                                : llvm::json::Value(nullptr);
            Values.push_back(std::move(Item));
          }
          if (!Values.empty())
            Entry["values"] = std::move(Values);
          Trace.push_back(std::move(Entry));
        }
        Record["trace"] = std::move(Trace);
      }
    }
    OS << llvm::formatv("{0}\n", llvm::json::Value(std::move(Record)));
  }

  void printDiagnostics(llvm::raw_ostream &OS) const {
    for (const auto &D : Diags) {
      if (Opts.Diagnostics == DiagnosticFormat::Json) {
        printJSONDiagnostic(D, OS);
        continue;
      }
      if (D.Loc.isValid()) {
        PresumedLoc PLoc = Ctx.getSourceManager().getPresumedLoc(D.Loc);
        if (PLoc.isValid())
          OS << PLoc.getFilename() << ":" << PLoc.getLine() << ":"
             << PLoc.getColumn() << ": ";
      }
      switch (D.K) {
      case VerifyDiagnostic::Lowered:
        OS << "Lowered: " << D.Message << "\n";
        break;
      case VerifyDiagnostic::Verified:
        OS << "Verified: " << D.Message << "\n";
        break;
      case VerifyDiagnostic::Error:
        OS << "error: " << D.Message << "\n";
        break;
      case VerifyDiagnostic::Unresolved:
        OS << "Unresolved: " << D.Message << "\n";
        break;
      case VerifyDiagnostic::BoundedSafe:
        OS << "BoundedSafe: " << D.Message << "\n";
        break;
      case VerifyDiagnostic::Exported:
        OS << "Exported: " << D.Message << "\n";
        break;
      case VerifyDiagnostic::Certified:
        OS << "Certified: " << D.Message << "\n";
        break;
      case VerifyDiagnostic::Warning:
        OS << "warning: " << D.Message << "\n";
        break;
      }
    }
  }
};

} // namespace

bool verify::verifyTranslationUnit(ASTContext &Ctx, llvm::raw_ostream &OS,
                                   const VerifyOptions &Opts) {
  Verifier V(Ctx, Opts, OS);
  bool Ok = V.run();
  V.printDiagnostics(OS);
  return Ok;
}