//===--- Verifier.cpp - CppVerify driver ----------------------------------===//
#include "Verifier.h"
#include "../Backend/CVC5Backend.h"
#include "../Backend/LeanBackend.h"
#include "../Backend/Obligation.h"
#include "../Backend/ObligationLowering.h"
#include "../Backend/ObligationSerialization.h"
#include "../Backend/ObligationSimplify.h"
#include "../Frontend/ASTConverter.h"
#include "../IR/VStmt.h"
#include "../Transform/LoopUnroll.h"
#include "../Transform/Origins.h"
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
#include "llvm/Support/ThreadPool.h"
#include "llvm/Support/raw_ostream.h"
#include <chrono>
#include <iterator>
#include <mutex>
#include <optional>
#include <tuple>

using namespace clang;
using namespace verify;

namespace {

/// The functions a body calls, whose contracts its proof assumes.
static void collectCallees(const std::vector<std::unique_ptr<VStmt>> &Stmts,
                           std::set<std::string> &Out) {
  for (const auto &S : Stmts) {
    switch (S->K) {
    case VStmt::Call:
      Out.insert(static_cast<const VCallStmt &>(*S).CalleeIdentity);
      break;
    case VStmt::If: {
      const auto &I = static_cast<const VIfStmt &>(*S);
      collectCallees(I.Then, Out);
      collectCallees(I.Else, Out);
      break;
    }
    case VStmt::While:
      collectCallees(static_cast<const VWhileStmt &>(*S).Body, Out);
      break;
    case VStmt::Seq:
      collectCallees(static_cast<const VSeqStmt &>(*S).Stmts, Out);
      break;
    case VStmt::GhostBlock:
      collectCallees(static_cast<const VGhostBlockStmt &>(*S).Body, Out);
      break;
    default:
      break;
    }
  }
}

/// A passive program asking whether its end is reachable: every assertion
/// becomes an assumption, and the end asserts false. With \p EntryOnly only
/// the precondition is kept.
/// Whether Goal holds after the entry assumptions, Extra, and the first
/// Count statements, every assertion among them assumed.
static PassiveProgram smokeProgram(const PassiveProgram &P, size_t Count,
                                   std::unique_ptr<VExpr> Goal,
                                   const VExpr *Extra = nullptr) {
  PassiveProgram Smoke;
  Smoke.FunctionName = P.FunctionName + ".smoke";
  Smoke.FunctionIdentity = P.FunctionIdentity + "::smoke";
  for (const auto &Assume : P.EntryAssumes)
    Smoke.EntryAssumes.push_back(cloneVExpr(Assume.get()));
  if (Extra)
    Smoke.EntryAssumes.push_back(cloneVExpr(Extra));
  for (size_t I = 0; I < Count && I < P.Stmts.size(); ++I) {
    auto Copy = std::make_unique<PassiveStmt>();
    Copy->K = PassiveStmt::Assume;
    Copy->Cond = cloneVExpr(P.Stmts[I]->Cond.get());
    Smoke.Stmts.push_back(std::move(Copy));
  }
  PassiveExitAssert End;
  End.ProofKind = ProofObligationKind::Assertion;
  End.Cond = std::move(Goal);
  Smoke.ExitAsserts.push_back(std::move(End));
  Smoke.ResultVarName = P.ResultVarName;
  Smoke.OldHeapName = P.OldHeapName;
  Smoke.HeapVariables = P.HeapVariables;
  Smoke.SpecFunctions = P.SpecFunctions;
  Smoke.SpecFuel = P.SpecFuel;
  Smoke.HiddenSpecs = P.HiddenSpecs;
  Smoke.RevealedSpecs = P.RevealedSpecs;
  Smoke.CallerIntMode = P.CallerIntMode;
  return Smoke;
}

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
    MixedProof,
    Trusted,
    Warning
  };
  Kind K;
  std::string Message;
  SourceLocation Loc;
  std::string FunctionName;
  std::optional<VerifyResult> Result;
  /// No execution reaches the claim, so it holds vacuously.
  bool Vacuous = false;
  /// Proved only for executions that terminate.
  bool Partial = false;
  /// Trusted contracts the proof relies on.
  std::vector<std::string> Trusts;
  /// Functions not verified that call this one: its precondition is assumed
  /// at those calls.
  std::vector<std::string> UnverifiedCallers;
  /// Kept for the steps that relate verdicts, but not printed: a proof the
  /// verifier generated, which is reported only if it fails.
  bool Quiet = false;
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
  case VerifyDiagnostic::MixedProof:
    return "mixed-proof";
  case VerifyDiagnostic::Trusted:
    return "trusted";
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
  case VerifyStatus::MixedProof:
    return "mixed-proof";
  }
  return "unresolved";
}

/// "[z3: 18 of 20 proved; lean: 2 exported]" for a Lean fallback.
static std::string evidenceSuffix(const ProofEvidence &Evidence,
                                  llvm::StringRef LeanState) {
  std::string Suffix = " [";
  if (Evidence.SolverProved)
    Suffix += Evidence.Solver + ": " + std::to_string(*Evidence.SolverProved) +
              " of " + std::to_string(Evidence.Total) + " proved; ";
  Suffix += "lean: " + std::to_string(Evidence.LeanObligations.size()) + " " +
            LeanState.str() + "]";
  return Suffix;
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

  /// The archive record of Module, empty without --obligation-out.
  llvm::Expected<std::string> archiveRecord(const ObligationModule &Module) {
    if (!Opts.ObligationOut)
      return std::string();

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
    return Serialized;
  }

  llvm::Error emitObligationArchive(const ObligationModule &Module) {
    llvm::Expected<std::string> Record = archiveRecord(Module);
    if (!Record)
      return Record.takeError();
    if (Opts.ObligationOut)
      *Opts.ObligationOut << *Record;
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
      std::string StableId =
          Module.FunctionIdentity + "::" + obligationKindName(Item.Kind) + "@";
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
        PP.ExitAsserts.push_back(
            {ProofObligationKind::Recommends, std::move(Inst)});
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
    const std::map<std::string, std::set<std::string>> UnverifiedCallers =
        Converter.getUnverifiedCallers();
    for (const auto &[Loc, Message] : Converter.getWarnings())
      Diags.push_back({VerifyDiagnostic::Warning, Message, Loc});
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
    Execution.CollectionTimeoutMs = Opts.CollectionTimeoutMs;
    Execution.SolverResourceLimit = Opts.SolverResourceLimit;
    Execution.MaxQueryNodes = Opts.MaxQueryNodes;
    Execution.IntegerEncoding = Opts.IntegerEncoding;
    Execution.SkipWholeModuleRetry = !Opts.LeanFallbackProjectPath.empty();
    Execution.CVC5Path = Opts.CVC5Path;
    Execution.ProfileQuantifiers = Opts.ProfileQuantifiers;
    Execution.ProofCachePath = Opts.ProofCachePath;
    Execution.ProofCacheMaxBytes = Opts.ProofCacheMaxBytes;
    Execution.ProofCacheMaxEntries = Opts.ProofCacheMaxEntries;
    // Functions are verified as tasks. With more than one job they run at
    // once on one pool of exactly that many workers, which the backends also
    // use for their obligations; each task has its own backends and buffers,
    // and the results are merged in source order. Lean exports stay serial.
    const unsigned Workers = llvm::heavyweight_hardware_concurrency(Opts.Jobs)
                                 .compute_thread_count();
    const bool Parallel = Workers > 1 && Opts.Backend != BackendKind::Lean &&
                          Opts.LeanFallbackProjectPath.empty() &&
                          !Opts.LeanCertify;
    Execution.Jobs = Workers;
    std::optional<llvm::StdThreadPool> Pool;
    if (Parallel) {
      Pool.emplace(llvm::heavyweight_hardware_concurrency(Workers));
      Execution.Pool = &*Pool;
    }
    std::unique_ptr<VerifyBackend> SharedBackend;
    if (!Parallel)
      SharedBackend = createVerifyBackend(
          Opts.Backend, LeanOut, Opts.BMCUnroll, Execution,
          Opts.LeanProjectPath.empty() ? nullptr : &LeanProjectGoals);
    std::unique_ptr<LeanVerifyBackend> LeanFallbackBackend;
    if (!Opts.LeanFallbackProjectPath.empty())
      LeanFallbackBackend = std::make_unique<LeanVerifyBackend>(
          LeanFile.get(), &LeanProjectGoals);
    // Vacuity checks: whether a verified function's end is reachable at all.
    // A vacuous path is refuted quickly; a satisfiable one is not worth
    // searching long, since an unsettled check only omits a warning.
    BackendExecutionOptions SmokeExecution = Execution;
    SmokeExecution.SolverTimeoutMs =
        Execution.SolverTimeoutMs == 0
            ? 1000
            : std::min<unsigned>(Execution.SolverTimeoutMs, 1000);
    SmokeExecution.CollectionTimeoutMs.reset();
    SmokeExecution.SingleQuery = true;
    SmokeExecution.Jobs = 1;
    SmokeExecution.Pool = nullptr;
    SmokeExecution.ProofCachePath.clear();
    auto falseGoal = [] {
      return std::make_unique<VLiteralExpr>(false, VType::makeBool(),
                                            SourceLocation());
    };
    const unsigned DumpLayers = Opts.DumpIRLayers;
    const bool MultiLayerDump = llvm::popcount(DumpLayers) > 1;
    bool AllOk = true;
    bool AnyFailed = false;
    std::set<std::string> FailedCallers;
    // A spec whose termination is not established has no definition, so a
    // proof that used it proves nothing.
    std::set<std::string> UndefinedSpecs;
    // Verdicts that assume callee contracts, and the callees they assume.
    std::vector<std::tuple<size_t, std::string, std::set<std::string>>>
        CallDependencies;
    // Frame facts of a spec whose reads clause is not established.
    std::set<std::string> UnframedSpecs;
    // Specs whose postcondition is not established.
    std::set<std::string> UnprovenPosts;
    // A verdict and the specs it relies on: their definitions and frames,
    // and their postconditions and unfoldings except where it withholds them.
    struct SpecReliance {
      size_t Index;
      std::set<std::string> Specs;
      std::set<std::string> Withheld;
    };
    std::vector<SpecReliance> ProofDependencies;
    // The line of each inductive predicate, which reports its rules.
    std::vector<std::pair<size_t, std::string>> InductiveLines;
    auto exportLeanFallbackTo = [&](std::vector<VerifyDiagnostic> &Out,
                                    const ObligationModule &Module,
                                    llvm::StringRef Label,
                                    const VerifyResult &SolverResult) {
      if (!LeanFallbackBackend)
        return false;
      const bool KnowsUnproved = SolverResult.UnprovedObligations &&
                                 !SolverResult.UnprovedObligations->empty();
      std::optional<std::set<std::string>> Selection;
      if (Opts.LeanScope == LeanFallbackScope::Unproved && KnowsUnproved)
        Selection.emplace(SolverResult.UnprovedObligations->begin(),
                          SolverResult.UnprovedObligations->end());
      ProofEvidence Evidence;
      Evidence.Solver = SolverResult.BackendName;
      Evidence.Total = Module.Obligations.size();
      if (KnowsUnproved)
        Evidence.SolverProved =
            Evidence.Total - SolverResult.UnprovedObligations->size();
      for (const Obligation &Item : Module.Obligations)
        if (!Selection || Selection->count(Item.Id))
          Evidence.LeanObligations.push_back(
              Item.StableId.empty() ? Item.Id : Item.StableId);
      LeanFallbackBackend->selectObligations(std::move(Selection));
      VerifyResult Fallback = LeanFallbackBackend->verify(Module);
      LeanFallbackBackend->selectObligations(std::nullopt);
      if (Fallback.Status == VerifyStatus::Exported) {
        std::string Message = "lean fallback: " + Label.str() +
                              evidenceSuffix(Evidence, "exported");
        Fallback.Evidence = std::move(Evidence);
        Out.push_back({VerifyDiagnostic::Exported, std::move(Message),
                       Fallback.Location, Label.str(), std::move(Fallback)});
        return true;
      }
      std::string Message = "lean fallback export failed: " + Label.str();
      if (!Fallback.Message.empty())
        Message += " (" + Fallback.Message + ")";
      Out.push_back({VerifyDiagnostic::Unresolved, std::move(Message),
                     Fallback.Location, Label.str(), std::move(Fallback)});
      return false;
    };

    struct FunctionRun {
      std::vector<VerifyDiagnostic> Diags;
      bool AllOk = true;
      bool AnyFailed = false;
      std::set<std::string> FailedCallers;
      std::set<std::string> UndefinedSpecs;
      std::vector<std::tuple<size_t, std::string, std::set<std::string>>>
          CallDependencies;
      std::set<std::string> UnframedSpecs;
      std::set<std::string> UnprovenPosts;
      std::vector<SpecReliance> ProofDependencies;
      std::vector<std::pair<size_t, std::string>> InductiveLines;
      std::string Dump;
      std::string Archive;
    };
    std::vector<FunctionRun> Runs(Functions.size());
    // The source manager caches its last line lookup.
    std::mutex SourceLock;
    auto verifyFunction = [&](size_t Index) {
      FunctionRun &Run = Runs[Index];
      std::vector<VerifyDiagnostic> &Diags = Run.Diags;
      bool &AllOk = Run.AllOk;
      bool &AnyFailed = Run.AnyFailed;
      std::set<std::string> &FailedCallers = Run.FailedCallers;
      std::set<std::string> &UndefinedSpecs = Run.UndefinedSpecs;
      auto &CallDependencies = Run.CallDependencies;
      std::set<std::string> &UnframedSpecs = Run.UnframedSpecs;
      std::set<std::string> &UnprovenPosts = Run.UnprovenPosts;
      auto &ProofDependencies = Run.ProofDependencies;
      auto &InductiveLines = Run.InductiveLines;
      llvm::raw_string_ostream DumpStream(Run.Dump);
      llvm::raw_ostream *DumpOS = this->DumpOS ? &DumpStream : nullptr;
      std::unique_ptr<VerifyBackend> OwnBackend;
      VerifyBackend *Backend = SharedBackend.get();
      if (Parallel) {
        OwnBackend = createVerifyBackend(Opts.Backend, LeanOut, Opts.BMCUnroll,
                                         Execution, nullptr);
        Backend = OwnBackend.get();
      }
      // One budget for every query of this function.
      std::optional<std::chrono::steady_clock::time_point> Deadline;
      if (Opts.FunctionTimeoutMs != 0)
        Deadline = std::chrono::steady_clock::now() +
                   std::chrono::milliseconds(Opts.FunctionTimeoutMs);
      Backend->setDeadline(Deadline);
      auto SmokeBackend = createVerifyBackend(BackendKind::Z3, nullptr, 0,
                                              SmokeExecution, nullptr);
      Passivizer P;
      P.setFunctionMap(InterfaceMap);
      auto proves = [&](PassiveProgram Smoke) {
        auto Lowered = buildObligationModule(Smoke);
        if (!Lowered) {
          llvm::consumeError(Lowered.takeError());
          return false;
        }
        auto Simplified = simplifyObligationModule(std::move(*Lowered));
        if (!Simplified) {
          llvm::consumeError(Simplified.takeError());
          return false;
        }
        return SmokeBackend->verify(*Simplified).Status ==
               VerifyStatus::Verified;
      };
      auto unreachable = [&](const PassiveProgram &Program, bool EntryOnly) {
        auto Lowered = buildObligationModule(smokeProgram(
            Program, EntryOnly ? 0 : Program.Stmts.size(), falseGoal()));
        if (!Lowered) {
          llvm::consumeError(Lowered.takeError());
          return false;
        }
        auto Simplified = simplifyObligationModule(std::move(*Lowered));
        if (!Simplified) {
          llvm::consumeError(Simplified.takeError());
          return false;
        }
        return SmokeBackend->verify(*Simplified).Status ==
               VerifyStatus::Verified;
      };

      auto recordDependencies = [&](const VFunction &Verified,
                                    const ObligationModule &Used) {
        std::set<std::string> Specs = Verified.SpecDependencies;
        for (const auto &[Identity, Function] : Used.LogicFunctions)
          Specs.insert(Identity);
        Specs.erase(Verified.Identity);
        // A rule's proof uses its predicate's definition, not its unfolding.
        Specs.erase(Verified.InductiveRuleOf);
        ProofDependencies.push_back(
            {Diags.size() - 1, std::move(Specs), Verified.FactsWithheld});
      };
      auto exportLeanFallback = [&](const ObligationModule &Module,
                                    llvm::StringRef Label,
                                    const VerifyResult &SolverResult) {
        return exportLeanFallbackTo(Diags, Module, Label, SolverResult);
      };
      auto emitObligationArchive =
          [&](const ObligationModule &Module) -> llvm::Error {
        llvm::Expected<std::string> Record = archiveRecord(Module);
        if (!Record)
          return Record.takeError();
        Run.Archive += *Record;
        return llvm::Error::success();
      };
      auto annotateObligationSources = [&](ObligationModule &Module) {
        std::lock_guard<std::mutex> Guard(SourceLock);
        this->annotateObligationSources(Module);
      };
      for (const auto &Fn :
           llvm::ArrayRef<std::unique_ptr<VFunction>>(&Functions[Index], 1)) {
        // The value of a spec outside its when domain, or a spec of
        // <cppverify.h>: nothing to verify but a library spec's termination,
        // which is reported only if it fails.
        if (Fn->Uninterpreted || (Fn->IsBuiltin && !Fn->NeedsDecreasesCheck))
          continue;
        if (Fn->IsExternalContract) {
          if (Fn->IsTrusted)
            Diags.push_back({VerifyDiagnostic::Trusted,
                             Fn->Name + " (contract assumed, not verified)",
                             Fn->DeclLoc, Fn->Name});
          else
            Diags.push_back(
                {VerifyDiagnostic::Warning,
                 Fn->Name + " has a contract but no definition, so its callers "
                            "are not verified; mark the declaration "
                            "[[cppverify::trusted]] to assume the contract",
                 Fn->DeclLoc, Fn->Name});
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
          annotatePointerOrigins(*PreparedFn);
          // `valid(p, n)` is a recognized UB marker. Discover it before spec
          // preparation folds its deliberately trivial body to `true`.
          // A generated proof about specs is not C++ code.
          if (Fn->TotalExpressions) {
          } else if (Opts.CheckUB && (isDeductiveBackend(Opts.Backend) ||
                                      Opts.Backend == BackendKind::BMC ||
                                      Opts.Backend == BackendKind::Lean)) {
            UBError = instrumentUBChecks(*PreparedFn);
          } else if (usesValidMarker(*Fn))
            Diags.push_back(
                {VerifyDiagnostic::Warning,
                 "contract of " + Fn->Name +
                     " uses the valid(p, n) extent marker, but memory "
                     "checking is disabled (--no-check-ub); the marker folds "
                     "to `true` and declared extents are not assumed, so "
                     "results about heap contents may be spurious.",
                 SourceLocation(), Fn->Name});
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
          Diags.push_back(
              {VerifyDiagnostic::Error, Fn->Name + ": " + *UBError});
          continue;
        }

        if (Fn->IsSpec && !Fn->Reads.empty()) {
          std::string Missing;
          PassiveProgram ReadsPP = buildReadsChecks(*Fn, FnMap, Missing);
          UnframedSpecs.insert(Fn->Identity);
          std::optional<ObligationModule> ReadsModule;
          std::string ReadsError;
          if (!Missing.empty()) {
            ReadsError = "calls " + Missing +
                         ", which reads the heap without a reads clause";
          } else if (auto Lowered = buildObligationModule(ReadsPP)) {
            if (auto Simplified = simplifyObligationModule(std::move(*Lowered)))
              ReadsModule = std::move(*Simplified);
            else
              ReadsError = llvm::toString(Simplified.takeError());
          } else {
            ReadsError = llvm::toString(Lowered.takeError());
          }
          if (!ReadsModule) {
            AllOk = false;
            AnyFailed = true;
            Diags.push_back(
                {VerifyDiagnostic::Error,
                 "spec reads failed: " + Fn->Name + " (" + ReadsError + ")",
                 SourceLocation(), Fn->Name});
          } else if (Opts.Backend == BackendKind::BMC) {
            ReadsModule->BMCTransform = BMCTransformProvenance{Opts.BMCUnroll};
          }
          if (ReadsModule) {
            annotateObligationSources(*ReadsModule);
            if (llvm::Error Error = emitObligationArchive(*ReadsModule)) {
              AllOk = false;
              AnyFailed = true;
              Diags.push_back(
                  {VerifyDiagnostic::Error,
                   "cannot serialize reads obligation: " + Fn->Name + " (" +
                       llvm::toString(std::move(Error)) + ")"});
              continue;
            }
            if (Opts.LowerOnly) {
              VerifyResult R =
                  lowerForBackend(*ReadsModule, Opts.Backend, Execution);
              if (R.Status == VerifyStatus::Lowered) {
                UnframedSpecs.erase(Fn->Identity);
                Diags.push_back({VerifyDiagnostic::Lowered,
                                 "spec reads: " + Fn->Name, R.Location,
                                 Fn->Name, R});
              } else {
                AllOk = false;
                AnyFailed = true;
                Diags.push_back({VerifyDiagnostic::Error,
                                 "lowering failed for reads: " + Fn->Name +
                                     backendSuffix(R),
                                 R.Location, Fn->Name, R});
              }
            } else {
              VerifyResult R = Backend->verify(*ReadsModule);
              if (R.Status == VerifyStatus::Verified ||
                  R.Status == VerifyStatus::Exported) {
                UnframedSpecs.erase(Fn->Identity);
                Diags.push_back({R.Status == VerifyStatus::Verified
                                     ? VerifyDiagnostic::Verified
                                     : VerifyDiagnostic::Exported,
                                 "spec reads: " + Fn->Name, R.Location,
                                 Fn->Name, R});
                recordDependencies(*Fn, *ReadsModule);
              } else {
                AllOk = false;
                AnyFailed = true;
                const bool IsUnresolved = R.Status == VerifyStatus::Unresolved;
                std::string Message =
                    std::string("spec reads ") +
                    (IsUnresolved ? "unresolved: " : "failed: ") + Fn->Name +
                    backendSuffix(R);
                if (!R.Message.empty())
                  Message += " (" + R.Message + ")";
                Diags.push_back({IsUnresolved ? VerifyDiagnostic::Unresolved
                                              : VerifyDiagnostic::Error,
                                 std::move(Message), R.Location, Fn->Name, R});
              }
            }
          }
        }

        // An inductive predicate's line stands for its rules, which its
        // generated proofs establish.
        if (Fn->Unfolding) {
          Diags.push_back({Opts.LowerOnly ? VerifyDiagnostic::Lowered
                           : Opts.Backend == BackendKind::Lean
                               ? VerifyDiagnostic::Exported
                               : VerifyDiagnostic::Verified,
                           "inductive predicate: " + Fn->Name});
          InductiveLines.emplace_back(Diags.size() - 1, Fn->Identity);
        }
        const bool Step = !Fn->InductiveStepOf.empty();
        if (Fn->IsSpec && !Fn->NeedsDecreasesCheck &&
            !Fn->Postconditions.empty() && !Step) {
          UnprovenPosts.insert(Fn->Identity);
          std::optional<ObligationModule> PostModule;
          std::string PostError;
          if (auto Lowered =
                  buildObligationModule(buildSpecPostChecks(*Fn, FnMap))) {
            if (auto Simplified = simplifyObligationModule(std::move(*Lowered)))
              PostModule = std::move(*Simplified);
            else
              PostError = llvm::toString(Simplified.takeError());
          } else {
            PostError = llvm::toString(Lowered.takeError());
          }
          if (!PostModule) {
            AllOk = false;
            AnyFailed = true;
            Diags.push_back({VerifyDiagnostic::Unresolved,
                             "obligation lowering failed for spec post: " +
                                 Fn->Name + " (" + PostError + ")"});
            continue;
          }
          if (Opts.Backend == BackendKind::BMC)
            PostModule->BMCTransform = BMCTransformProvenance{Opts.BMCUnroll};
          annotateObligationSources(*PostModule);
          if (llvm::Error Error = emitObligationArchive(*PostModule)) {
            AllOk = false;
            AnyFailed = true;
            Diags.push_back(
                {VerifyDiagnostic::Error,
                 "cannot serialize spec post obligation: " + Fn->Name + " (" +
                     llvm::toString(std::move(Error)) + ")"});
            continue;
          }
          if (Opts.LowerOnly) {
            VerifyResult R =
                lowerForBackend(*PostModule, Opts.Backend, Execution);
            if (R.Status == VerifyStatus::Lowered) {
              UnprovenPosts.erase(Fn->Identity);
              Diags.push_back({VerifyDiagnostic::Lowered,
                               "spec post: " + Fn->Name, R.Location, Fn->Name,
                               R});
            } else {
              AllOk = false;
              AnyFailed = true;
              Diags.push_back({VerifyDiagnostic::Error,
                               "lowering failed for spec post: " + Fn->Name +
                                   backendSuffix(R),
                               R.Location, Fn->Name, R});
            }
            continue;
          }
          VerifyResult R = Backend->verify(*PostModule);
          if (R.Status == VerifyStatus::Verified ||
              R.Status == VerifyStatus::Exported) {
            UnprovenPosts.erase(Fn->Identity);
            Diags.push_back({R.Status == VerifyStatus::Verified
                                 ? VerifyDiagnostic::Verified
                                 : VerifyDiagnostic::Exported,
                             "spec post: " + Fn->Name, R.Location, Fn->Name,
                             R});
            recordDependencies(*Fn, *PostModule);
          } else {
            AllOk = false;
            AnyFailed = true;
            const bool IsUnresolved = R.Status == VerifyStatus::Unresolved;
            std::string Message = std::string("spec post ") +
                                  (IsUnresolved ? "unresolved: " : "failed: ") +
                                  Fn->Name + backendSuffix(R);
            if (!R.Message.empty())
              Message += " (" + R.Message + ")";
            Diags.push_back({IsUnresolved ? VerifyDiagnostic::Unresolved
                                          : VerifyDiagnostic::Error,
                             std::move(Message), R.Location, Fn->Name, R});
          }
          continue;
        }

        if (Fn->IsSpec && !Fn->NeedsDecreasesCheck && !Step) {
          const VerifyDiagnostic::Kind Kind =
              Opts.LowerOnly ? VerifyDiagnostic::Lowered
                             : (Opts.Backend == BackendKind::Lean
                                    ? VerifyDiagnostic::Exported
                                    : VerifyDiagnostic::Verified);
          if (Fn->IsConstexprSpec)
            Diags.push_back({Kind, "constexpr spec axiom: " + Fn->Name});
          else if (!Fn->Unfolding)
            Diags.push_back({Kind, "spec axiom: " + Fn->Name});
          continue;
        }

        // Executable and proof recursion is checked at each call in the
        // function's own obligations; a spec's definition cannot help prove its
        // termination, so it is checked separately.
        // A step function of an inductive predicate terminates whatever its
        // postconditions say, so they are proved apart: by induction on the
        // height, with its definition known, which its own termination check
        // establishes. Only a failure is reported.
        if (Step && !Fn->Postconditions.empty()) {
          UnprovenPosts.insert(Fn->Identity);
          const std::string Label = "spec post by induction";
          std::optional<ObligationModule> Induction;
          std::string Error;
          if (auto Lowered =
                  buildObligationModule(buildInductionChecks(*Fn, FnMap))) {
            if (auto Simplified = simplifyObligationModule(std::move(*Lowered)))
              Induction = std::move(*Simplified);
            else
              Error = llvm::toString(Simplified.takeError());
          } else {
            Error = llvm::toString(Lowered.takeError());
          }
          if (!Induction) {
            AllOk = false;
            AnyFailed = true;
            Diags.push_back({VerifyDiagnostic::Unresolved,
                             "obligation lowering failed for " + Label + ": " +
                                 Fn->InductiveStepOf + " (" + Error + ")"});
          } else {
            if (Opts.Backend == BackendKind::BMC)
              Induction->BMCTransform = BMCTransformProvenance{Opts.BMCUnroll};
            annotateObligationSources(*Induction);
            if (llvm::Error Error = emitObligationArchive(*Induction)) {
              AllOk = false;
              AnyFailed = true;
              Diags.push_back({VerifyDiagnostic::Error,
                               "cannot serialize " + Label + " obligation: " +
                                   Fn->InductiveStepOf + " (" +
                                   llvm::toString(std::move(Error)) + ")"});
            } else if (Opts.LowerOnly) {
              VerifyResult R =
                  lowerForBackend(*Induction, Opts.Backend, Execution);
              if (R.Status == VerifyStatus::Lowered) {
                UnprovenPosts.erase(Fn->Identity);
              } else {
                AllOk = false;
                AnyFailed = true;
                Diags.push_back({VerifyDiagnostic::Error,
                                 "lowering failed for " + Label + ": " +
                                     Fn->InductiveStepOf + backendSuffix(R),
                                 R.Location, Fn->Name, R});
              }
            } else {
              VerifyResult R = Backend->verify(*Induction);
              if (R.Status == VerifyStatus::Verified ||
                  R.Status == VerifyStatus::Exported) {
                UnprovenPosts.erase(Fn->Identity);
                Diags.push_back({R.Status == VerifyStatus::Verified
                                     ? VerifyDiagnostic::Verified
                                     : VerifyDiagnostic::Exported,
                                 Label + ": " + Fn->InductiveStepOf, R.Location,
                                 Fn->Name, R});
                Diags.back().Quiet = true;
                // The proof uses the definition, so it rests on termination.
                recordDependencies(*Fn, *Induction);
                ProofDependencies.back().Specs.insert(Fn->Identity);
              } else {
                AllOk = false;
                AnyFailed = true;
                const bool IsUnresolved = R.Status == VerifyStatus::Unresolved;
                std::string Message =
                    Label + (IsUnresolved ? " unresolved: " : " failed: ") +
                    Fn->InductiveStepOf + backendSuffix(R);
                if (!R.Message.empty())
                  Message += " (" + R.Message + ")";
                Diags.push_back({IsUnresolved ? VerifyDiagnostic::Unresolved
                                              : VerifyDiagnostic::Error,
                                 std::move(Message), R.Location, Fn->Name, R});
              }
            }
          }
        }

        if (Step && !Fn->NeedsDecreasesCheck)
          continue;
        if (Fn->NeedsDecreasesCheck && Fn->IsSpec) {
          std::optional<VFunction> Bare;
          if (Step && !Fn->Postconditions.empty()) {
            Bare = cloneVFunction(*Fn);
            Bare->Postconditions.clear();
            Bare->PostconditionKinds.clear();
          }
          PassiveProgram DecPP =
              buildDecreasesChecks(Bare ? *Bare : *Fn, FnMap);
          auto DecModuleOrErr = buildObligationModule(DecPP);
          // A spec's postcondition is proved with its termination.
          const std::string &Shown = Step ? Fn->InductiveStepOf : Fn->Name;
          const bool Quiet = Fn->IsBuiltin || Step;
          const std::string DecLabel = !Step && !Fn->Postconditions.empty()
                                           ? "spec decreases and post: "
                                           : "spec decreases: ";
          UndefinedSpecs.insert(Fn->Identity);
          if (!Step && !Fn->Postconditions.empty())
            UnprovenPosts.insert(Fn->Identity);
          if (!DecModuleOrErr) {
            AllOk = false;
            AnyFailed = true;
            Diags.push_back(
                {VerifyDiagnostic::Unresolved,
                 "obligation lowering failed for decreases: " + Shown + " (" +
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
                 "obligation simplification failed for decreases: " + Shown +
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
            Diags.push_back({VerifyDiagnostic::Error,
                             "cannot serialize decreases obligation: " + Shown +
                                 " (" + llvm::toString(std::move(Error)) +
                                 ")"});
            continue;
          }
          if (Opts.LowerOnly) {
            VerifyResult DR =
                lowerForBackend(DecModule, Opts.Backend, Execution);
            if (DR.Status != VerifyStatus::Lowered) {
              AllOk = false;
              AnyFailed = true;
              std::string Message =
                  std::string(Opts.Backend == BackendKind::Z3 ||
                                      Opts.Backend == BackendKind::BMC
                                  ? "Z3"
                                  : "backend") +
                  " lowering failed for decreases: " + Shown;
              Message += backendSuffix(DR);
              if (!DR.Message.empty())
                Message += " (" + DR.Message + ")";
              Diags.push_back({VerifyDiagnostic::Error, std::move(Message),
                               DR.Location, Fn->Name, std::move(DR)});
              continue;
            }
            if (Fn->IsSpec) {
              if (!Step)
                UnprovenPosts.erase(Fn->Identity);
              if (!Quiet)
                Diags.push_back({VerifyDiagnostic::Lowered, DecLabel + Shown,
                                 SourceLocation(), Fn->Name, DR});
              continue;
            }
          } else {
            VerifyResult R = Backend->verify(DecModule);
            if (Fn->IsSpec && (R.Reason == VerifyReason::SpecHidden ||
                               R.Reason == VerifyReason::SpecFuel)) {
              // The function is opaque in its own termination check.
              std::string Rule =
                  "a definition cannot be used to prove its own termination, "
                  "so every recursive call of " +
                  Fn->Name +
                  " must decrease the measure whatever its other calls return";
              R.Message = R.Reason == VerifyReason::SpecHidden
                              ? std::move(Rule)
                              : Rule + " (" + R.Message + ")";
            }
            if (R.Status == VerifyStatus::Exported) {
              if (!Quiet)
                Diags.push_back({VerifyDiagnostic::Exported,
                                 "decreases: " + Shown, R.Location, Fn->Name,
                                 R});
              if (Fn->IsSpec) {
                UndefinedSpecs.erase(Fn->Identity);
                if (!Step)
                  UnprovenPosts.erase(Fn->Identity);
                continue;
              }
            } else if (R.Status == VerifyStatus::Verified) {
              if (Fn->IsSpec) {
                UndefinedSpecs.erase(Fn->Identity);
                if (!Step)
                  UnprovenPosts.erase(Fn->Identity);
                if (!Quiet)
                  Diags.push_back({VerifyDiagnostic::Verified, DecLabel + Shown,
                                   R.Location, Fn->Name, R});
                recordDependencies(*Fn, DecModule);
                continue;
              }
            } else {
              const bool IsUnresolved = R.Status == VerifyStatus::Unresolved;
              const bool FallbackExported =
                  IsUnresolved &&
                  exportLeanFallback(DecModule, "decreases: " + Fn->Name, R);
              if (Opts.LeanCertify && FallbackExported) {
                if (Fn->IsSpec) {
                  UndefinedSpecs.erase(Fn->Identity);
                  UnprovenPosts.erase(Fn->Identity);
                  continue;
                }
              } else {
                AllOk = false;
                AnyFailed = true;
                if (!Fn->IsProof)
                  FailedCallers.insert(Fn->Identity);
                std::string Message =
                    std::string(Fn->IsSpec
                                    ? DecLabel.substr(0, DecLabel.size() - 2) +
                                          " "
                                    : "decreases ") +
                    (IsUnresolved ? "unresolved: " : "failed: ") + Shown +
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
                       llvm::toString(SimplifiedBoundModule.takeError()) +
                       ")"});
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

        PassiveProgram PP =
            BMCProgram ? std::move(*BMCProgram) : P.run(*WorkFn);
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
                                 llvm::toString(ModuleOrErr.takeError()) +
                                 ")"});
            continue;
          }
          auto SimplifiedModule = simplifyObligationModule(
              std::move(*ModuleOrErr), &Simplification);
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
          VerifyResult Lowered =
              lowerObligationModule(Module, DumpOS, Execution);
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
          VerifyResult Lowered =
              lowerForBackend(Module, Opts.Backend, Execution);
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
                  : (Opts.Backend == BackendKind::Portfolio ? "portfolio"
                                                            : "z3");
          Diags.push_back({VerifyDiagnostic::Lowered, Fn->Name,
                           SourceLocation(), Fn->Name, std::move(Result)});
          continue;
        }

        VerifyResult R =
            BMCResult ? std::move(*BMCResult) : Backend->verify(Module);
        if (R.Status == VerifyStatus::Verified ||
            R.Status == VerifyStatus::Certified) {
          Diags.push_back(
              {R.Status == VerifyStatus::Verified ? VerifyDiagnostic::Verified
                                                  : VerifyDiagnostic::Certified,
               Fn->Name + backendSuffix(R), R.Location, Fn->Name, R});
          recordDependencies(*Fn, BMCModule ? *BMCModule : Module);
          std::set<std::string> Callees;
          collectCallees(Fn->Body, Callees);
          CallDependencies.emplace_back(Diags.size() - 1, Fn->Identity,
                                        std::move(Callees));
          const bool Rule = !Fn->InductiveRuleOf.empty();
          Diags.back().Quiet = Rule;
          // A proof that no execution reaches the end says nothing.
          const bool Smoke =
              !BMCResult && Opts.Backend != BackendKind::Lean && !Rule;
          bool WhollyVacuous = false;
          if (Smoke && unreachable(PP, /*EntryOnly=*/false)) {
            WhollyVacuous = true;
            const size_t Verdict = Diags.size() - 1;
            Diags[Verdict].Message += " [vacuous]";
            Diags[Verdict].Vacuous = true;
            Diags.push_back(
                {VerifyDiagnostic::Warning,
                 unreachable(PP, /*EntryOnly=*/true)
                     ? Fn->Name + ": the precondition is unsatisfiable, so "
                                  "every claim about it holds vacuously"
                     : Fn->Name + ": no execution reaches the end, so its "
                                  "postcondition holds vacuously; check the "
                                  "contracts it calls and its assumptions",
                 R.Location, Fn->Name});
          }
          if (Smoke && !WhollyVacuous) {
            const size_t Verdict = Diags.size() - 1;
            // A behavior that never applies has its postconditions unchecked.
            for (const auto &[Name, Assumes] : PP.BehaviorAssumes)
              if (proves(smokeProgram(PP, 0, falseGoal(), Assumes.get())))
                Diags.push_back(
                    {VerifyDiagnostic::Warning,
                     Fn->Name + ": behavior " + Name +
                         " never applies: its assumption contradicts the "
                         "preconditions, so its postconditions are never "
                         "checked",
                     Assumes->Loc, Fn->Name});
            // A trusted contract that contradicts the state of a call makes
            // everything after the call hold vacuously.
            for (size_t I = 0; I < PP.Stmts.size(); ++I) {
              const PassiveStmt &Post = *PP.Stmts[I];
              if (Post.TrustedCallee.empty() || !Post.CallGuard)
                continue;
              auto unreached = [&](size_t Count) {
                return proves(smokeProgram(
                    PP, Count,
                    std::make_unique<VUnaryOpExpr>(
                        VUnaryOp::Not, cloneVExpr(Post.CallGuard.get()),
                        VType::makeBool(), Post.CallLoc)));
              };
              if (!unreached(I + Post.PostClauses) || unreached(I))
                continue;
              if (!Diags[Verdict].Vacuous) {
                Diags[Verdict].Message += " [vacuous]";
                Diags[Verdict].Vacuous = true;
              }
              Diags.push_back(
                  {VerifyDiagnostic::Warning,
                   Fn->Name + ": the trusted contract of " +
                       Post.TrustedCallee +
                       " contradicts the state of this call, so everything "
                       "after it holds vacuously",
                   Post.CallLoc, Fn->Name});
            }
          }
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
                                        exportLeanFallback(Module, Fn->Name, R);
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
      DumpStream.flush();
    };
    if (Parallel) {
      llvm::ThreadPoolTaskGroup Group(*Pool);
      for (size_t I = 0; I != Functions.size(); ++I)
        Group.async([&verifyFunction, I] { verifyFunction(I); });
      Group.wait();
    } else {
      for (size_t I = 0; I != Functions.size(); ++I)
        verifyFunction(I);
    }
    for (FunctionRun &Run : Runs) {
      const size_t Base = Diags.size();
      for (VerifyDiagnostic &D : Run.Diags)
        Diags.push_back(std::move(D));
      AllOk &= Run.AllOk;
      AnyFailed |= Run.AnyFailed;
      FailedCallers.insert(Run.FailedCallers.begin(), Run.FailedCallers.end());
      UndefinedSpecs.insert(Run.UndefinedSpecs.begin(),
                            Run.UndefinedSpecs.end());
      UnframedSpecs.insert(Run.UnframedSpecs.begin(), Run.UnframedSpecs.end());
      UnprovenPosts.insert(Run.UnprovenPosts.begin(), Run.UnprovenPosts.end());
      for (auto &[Index, Identity, Callees] : Run.CallDependencies)
        CallDependencies.emplace_back(Base + Index, std::move(Identity),
                                      std::move(Callees));
      for (SpecReliance &Reliance : Run.ProofDependencies)
        ProofDependencies.push_back({Base + Reliance.Index,
                                     std::move(Reliance.Specs),
                                     std::move(Reliance.Withheld)});
      for (auto &[Index, Identity] : Run.InductiveLines)
        InductiveLines.emplace_back(Base + Index, std::move(Identity));
      if (DumpOS)
        *DumpOS << Run.Dump;
      if (Opts.ObligationOut)
        *Opts.ObligationOut << Run.Archive;
    }

    for (const auto &[Index, Specs, Withheld] : ProofDependencies) {
      std::string Undefined;
      std::string Unframed;
      std::string Unproven;
      for (const std::string &Identity : Specs) {
        auto It = FnMap.find(Identity);
        const std::string &Name =
            It != FnMap.end() ? It->second->Name : Identity;
        if (UndefinedSpecs.count(Identity))
          Undefined += (Undefined.empty() ? "" : ", ") + Name;
        else if (UnframedSpecs.count(Identity))
          Unframed += (Unframed.empty() ? "" : ", ") + Name;
        else if (UnprovenPosts.count(Identity) && !Withheld.count(Identity))
          Unproven += (Unproven.empty() ? "" : ", ") + Name;
      }
      if (Undefined.empty() && Unframed.empty() && Unproven.empty())
        continue;
      VerifyDiagnostic &Diagnostic = Diags[Index];
      AllOk = false;
      Diagnostic.K = VerifyDiagnostic::Unresolved;
      if (!Undefined.empty())
        Diagnostic.Message += " [reason=spec.termination] (relies on the "
                              "definition of " +
                              Undefined +
                              ", whose termination is not established)";
      else if (!Unframed.empty())
        Diagnostic.Message += " [reason=spec.reads] (relies on the reads "
                              "clause of " +
                              Unframed + ", which is not established)";
      else
        Diagnostic.Message += " [reason=spec.post] (relies on the "
                              "postcondition of " +
                              Unproven + ", which is not established)";
      if (Diagnostic.Result) {
        Diagnostic.Result->Status = VerifyStatus::Unresolved;
        Diagnostic.Result->Reason =
            !Undefined.empty()  ? VerifyReason::SpecTermination
            : !Unframed.empty() ? VerifyReason::SpecReads
                                : VerifyReason::SpecPost;
      }
    }

    // Total correctness needs every loop to terminate. A bounded proof
    // proves its unwinding, so every loop there exits within the bound.
    for (const auto &[Index, Identity, Callees] : CallDependencies) {
      VerifyDiagnostic &Diagnostic = Diags[Index];
      auto It = FnMap.find(Identity);
      if (It == FnMap.end() || It->second->UnmeasuredLoop.isInvalid() ||
          (Diagnostic.K != VerifyDiagnostic::Verified &&
           Diagnostic.K != VerifyDiagnostic::Certified) ||
          (Diagnostic.Result && Diagnostic.Result->Bound))
        continue;
      AllOk = false;
      const SourceLocation Loop = It->second->UnmeasuredLoop;
      const PresumedLoc Where = Ctx.getSourceManager().getPresumedLoc(Loop);
      Diagnostic.K = VerifyDiagnostic::Unresolved;
      Diagnostic.Loc = Loop;
      Diagnostic.Message +=
          " [reason=decreases.missing] (the loop at " +
          (Where.isValid() ? std::to_string(Where.getLine()) + ":" +
                                 std::to_string(Where.getColumn())
                           : std::string("?")) +
          " has no decreases clause: give it a measure, or decreases(*) to "
          "allow it to diverge)";
      if (Diagnostic.Result) {
        Diagnostic.Result->Status = VerifyStatus::Unresolved;
        Diagnostic.Result->Reason = VerifyReason::DecreasesMissing;
      }
    }

    // A verdict that assumes a callee's contract is a proof only once the
    // callee establishes it.
    std::set<std::string> Unestablished;
    for (const auto &Fn : Functions)
      if (!Fn->IsSpec && !Fn->Uninterpreted && !Fn->IsTrusted)
        Unestablished.insert(Fn->Identity);
    for (const auto &[Index, Identity, Callees] : CallDependencies)
      if (Diags[Index].K == VerifyDiagnostic::Verified ||
          Diags[Index].K == VerifyDiagnostic::Certified)
        Unestablished.erase(Identity);
    auto settleCallees = [&] {
      for (bool Changed = true; Changed;) {
        Changed = false;
        for (const auto &[Index, Identity, Callees] : CallDependencies) {
          VerifyDiagnostic &Diagnostic = Diags[Index];
          if (Diagnostic.K != VerifyDiagnostic::Verified &&
              Diagnostic.K != VerifyDiagnostic::Certified)
            continue;
          std::string Names;
          for (const std::string &Callee : Callees)
            if (Callee != Identity && Unestablished.count(Callee)) {
              auto It = FnMap.find(Callee);
              Names += (Names.empty() ? "" : ", ") +
                       (It != FnMap.end() ? It->second->Name : Callee);
              if (It != FnMap.end() && It->second->IsExternalContract)
                Names += " (no definition; mark it [[cppverify::trusted]] to "
                         "assume it)";
            }
          if (Names.empty())
            continue;
          AllOk = false;
          Diagnostic.K = VerifyDiagnostic::Unresolved;
          Diagnostic.Message += " [reason=callee.contract] (relies on the "
                                "contract of " +
                                Names + ", which is not established)";
          if (Diagnostic.Result) {
            Diagnostic.Result->Status = VerifyStatus::Unresolved;
            Diagnostic.Result->Reason = VerifyReason::CalleeContract;
          }
          Unestablished.insert(Identity);
          Changed = true;
        }
      }
    };
    settleCallees();

    // An inductive predicate's unfolding is a fact only once its rules are
    // proved: a verdict that relies on it otherwise proves nothing, and the
    // rules of predicates it is used in may in turn be left unproved.
    std::map<std::string, std::vector<const VFunction *>> RulesOf;
    for (const auto &Fn : Functions)
      if (!Fn->InductiveRuleOf.empty())
        RulesOf[Fn->InductiveRuleOf].push_back(Fn.get());
    std::map<size_t, std::string> VerdictOf;
    for (const auto &[Index, Identity, Callees] : CallDependencies)
      VerdictOf[Index] = Identity;
    auto demoteForRules = [&](VerifyDiagnostic &Diagnostic,
                              const std::string &Why) {
      AllOk = false;
      Diagnostic.K = VerifyDiagnostic::Unresolved;
      Diagnostic.Message += " [reason=spec.inductive] (" + Why + ")";
      if (Diagnostic.Result) {
        Diagnostic.Result->Status = VerifyStatus::Unresolved;
        Diagnostic.Result->Reason = VerifyReason::SpecInductive;
      }
    };
    for (bool Changed = !RulesOf.empty(); Changed;) {
      Changed = false;
      std::map<std::string, std::string> Unproved;
      for (const auto &[Predicate, Rules] : RulesOf)
        for (const VFunction *Rule : Rules)
          if (Unestablished.count(Rule->Identity)) {
            std::string &Names = Unproved[Predicate];
            const size_t Open = Rule->Name.rfind(" (");
            Names += (Names.empty() ? "" : ", ") +
                     (Open == std::string::npos
                          ? Rule->Name
                          : Rule->Name.substr(Open + 2,
                                              Rule->Name.size() - Open - 3));
          }
      for (const auto &[Index, Specs, Withheld] : ProofDependencies) {
        VerifyDiagnostic &Diagnostic = Diags[Index];
        if (Diagnostic.K != VerifyDiagnostic::Verified &&
            Diagnostic.K != VerifyDiagnostic::Certified)
          continue;
        std::string Names;
        for (const std::string &Identity : Specs)
          if (Unproved.count(Identity) && !Withheld.count(Identity)) {
            auto It = FnMap.find(Identity);
            Names += (Names.empty() ? "" : ", ") +
                     (It != FnMap.end() ? It->second->Name : Identity);
          }
        if (Names.empty())
          continue;
        demoteForRules(Diagnostic, "relies on the unfolding of " + Names +
                                       ", whose rules are not established");
        if (auto It = VerdictOf.find(Index); It != VerdictOf.end())
          Unestablished.insert(It->second);
        Changed = true;
      }
      for (const auto &[Index, Identity] : InductiveLines) {
        VerifyDiagnostic &Diagnostic = Diags[Index];
        auto It = Unproved.find(Identity);
        if (It != Unproved.end() && Diagnostic.K == VerifyDiagnostic::Verified)
          demoteForRules(Diagnostic,
                         "its rules are not established: " + It->second);
      }
      if (Changed)
        settleCallees();
    }
    // A proof trusts what its callees' proofs trust, too.
    std::map<std::string, std::set<std::string>> Trusts;
    for (bool Changed = true; Changed;) {
      Changed = false;
      for (const auto &[Index, Identity, Callees] : CallDependencies) {
        std::set<std::string> &Mine = Trusts[Identity];
        const size_t Before = Mine.size();
        for (const std::string &Callee : Callees) {
          auto It = FnMap.find(Callee);
          if (It == FnMap.end() || Callee == Identity)
            continue;
          if (It->second->IsTrusted)
            Mine.insert(It->second->Name);
          if (auto Inherited = Trusts.find(Callee); Inherited != Trusts.end())
            Mine.insert(Inherited->second.begin(), Inherited->second.end());
        }
        Changed |= Mine.size() != Before;
      }
    }
    for (const auto &[Index, Identity, Callees] : CallDependencies) {
      VerifyDiagnostic &Diagnostic = Diags[Index];
      if (Diagnostic.K != VerifyDiagnostic::Verified &&
          Diagnostic.K != VerifyDiagnostic::Certified)
        continue;
      std::string Trusted;
      for (const std::string &Name : Trusts[Identity]) {
        Trusted += (Trusted.empty() ? "" : ",") + Name;
        Diagnostic.Trusts.push_back(Name);
      }
      if (!Trusted.empty())
        Diagnostic.Message += " [trusts=" + Trusted + "]";
    }
    // Calls from code that is not verified rely on the precondition without
    // checking it, so the proof holds only where they establish it.
    for (const auto &[Index, Identity, Callees] : CallDependencies) {
      VerifyDiagnostic &Diagnostic = Diags[Index];
      auto Callers = UnverifiedCallers.find(Identity);
      auto Fn = FnMap.find(Identity);
      if (Callers == UnverifiedCallers.end() || Fn == FnMap.end() ||
          llvm::none_of(
              Fn->second->Preconditions,
              [](const std::unique_ptr<VExpr> &Pre) {
                return Pre->K != VExpr::Literal ||
                       static_cast<const VLiteralExpr &>(*Pre).Value != "1";
              }) ||
          (Diagnostic.K != VerifyDiagnostic::Verified &&
           Diagnostic.K != VerifyDiagnostic::Certified))
        continue;
      std::string Names;
      for (const std::string &Name : Callers->second) {
        Names += (Names.empty() ? "" : ", ") + Name;
        Diagnostic.UnverifiedCallers.push_back(Name);
      }
      Diagnostic.Message += " (its precondition is assumed, not checked, at "
                            "calls from unverified " +
                            Names + ")";
    }

    // decreases(*) allows divergence, and so does calling a function that
    // may diverge: such a proof covers only the executions that terminate.
    std::map<std::string, std::string> Diverges;
    for (const auto &Fn : Functions)
      if (Fn->DivergenceLoc.isValid()) {
        const PresumedLoc Where =
            Ctx.getSourceManager().getPresumedLoc(Fn->DivergenceLoc);
        Diverges[Fn->Identity] =
            "decreases(*) at " +
            (Where.isValid() ? std::to_string(Where.getLine()) + ":" +
                                   std::to_string(Where.getColumn())
                             : std::string("?")) +
            " allows it to diverge";
      }
    for (bool Changed = true; Changed;) {
      Changed = false;
      for (const auto &Fn : Functions) {
        if (Fn->IsSpec || Fn->IsProof || Diverges.count(Fn->Identity))
          continue;
        std::set<std::string> Callees;
        collectCallees(Fn->Body, Callees);
        for (const std::string &Callee : Callees)
          if (auto It = Diverges.find(Callee); It != Diverges.end()) {
            auto Target = FnMap.find(Callee);
            Diverges[Fn->Identity] =
                "it calls " +
                (Target != FnMap.end() ? Target->second->Name : Callee) +
                ", which may diverge";
            Changed = true;
            break;
          }
      }
    }
    for (const auto &[Index, Identity, Callees] : CallDependencies) {
      VerifyDiagnostic &Diagnostic = Diags[Index];
      auto It = Diverges.find(Identity);
      if (It == Diverges.end() ||
          (Diagnostic.K != VerifyDiagnostic::Verified &&
           Diagnostic.K != VerifyDiagnostic::Certified))
        continue;
      Diagnostic.Message += " [partial]";
      Diagnostic.Partial = true;
      Diags.push_back({VerifyDiagnostic::Warning,
                       Diagnostic.FunctionName +
                           ": proved only for executions that terminate: " +
                           It->second,
                       SourceLocation(), Diagnostic.FunctionName});
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
            const ProofEvidence *Evidence =
                Diagnostic.Result && Diagnostic.Result->Evidence
                    ? &*Diagnostic.Result->Evidence
                    : nullptr;
            if (Evidence &&
                Evidence->LeanObligations.size() < Evidence->Total) {
              // Only a complete split of the obligations is a proof.
              if (!Evidence->SolverProved ||
                  *Evidence->SolverProved + Evidence->LeanObligations.size() !=
                      Evidence->Total) {
                AllOk = false;
                Diagnostic.K = VerifyDiagnostic::Unresolved;
                Diagnostic.Message += " (inconsistent proof evidence)";
                Diagnostic.Result->Status = VerifyStatus::Unresolved;
                Diagnostic.Result->Reason = VerifyReason::InvalidBackendResult;
                continue;
              }
              Diagnostic.K = VerifyDiagnostic::MixedProof;
              Diagnostic.Message = Diagnostic.FunctionName +
                                   evidenceSuffix(*Evidence, "certified");
              Diagnostic.Result->Status = VerifyStatus::MixedProof;
              Diagnostic.Result->BackendName = Evidence->Solver + "+lean";
              Diagnostic.Result->Reason = VerifyReason::None;
              continue;
            }
            Diagnostic.K = VerifyDiagnostic::Certified;
            llvm::StringRef Name = Diagnostic.Message;
            if (!Name.consume_front("lean obligation: ")) {
              Name.consume_front("lean fallback: ");
              Name = Name.substr(0, Name.find(" ["));
            }
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

    if (D.Vacuous)
      Record["vacuous"] = true;
    if (D.Partial)
      Record["partial"] = true;
    if (!D.Trusts.empty()) {
      llvm::json::Array Trusted;
      for (const std::string &Name : D.Trusts)
        Trusted.push_back(jsonText(Name));
      Record["trusts"] = std::move(Trusted);
    }
    if (!D.UnverifiedCallers.empty()) {
      llvm::json::Array Callers;
      for (const std::string &Name : D.UnverifiedCallers)
        Callers.push_back(jsonText(Name));
      Record["unverified_callers"] = std::move(Callers);
    }
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
      if (!Result.QuantifierProfile.empty()) {
        llvm::json::Array Quantifiers;
        for (const QuantifierProfileEntry &Entry : Result.QuantifierProfile) {
          llvm::json::Object Item;
          Item["line"] = static_cast<int64_t>(Entry.Line);
          Item["column"] = static_cast<int64_t>(Entry.Column);
          Item["instances"] = static_cast<int64_t>(Entry.Instances);
          Item["max_generation"] = static_cast<int64_t>(Entry.MaxGeneration);
          Quantifiers.push_back(std::move(Item));
        }
        Record["quantifier_profile"] = std::move(Quantifiers);
      }
      if (Result.Evidence) {
        llvm::json::Object Evidence;
        Evidence["solver"] = Result.Evidence->Solver;
        Evidence["total"] = static_cast<int64_t>(Result.Evidence->Total);
        Evidence["solver_proved"] =
            Result.Evidence->SolverProved
                ? llvm::json::Value(
                      static_cast<int64_t>(*Result.Evidence->SolverProved))
                : llvm::json::Value(nullptr);
        llvm::json::Array Lean;
        for (const std::string &Id : Result.Evidence->LeanObligations)
          Lean.push_back(jsonText(Id));
        Evidence["lean"] = std::move(Lean);
        Record["evidence"] = std::move(Evidence);
      }
      if (!Result.ObligationId.empty()) {
        llvm::json::Object Obligation;
        Obligation["id"] = jsonText(Result.ObligationId);
        if (Result.ObligationType)
          Obligation["kind"] = obligationKindName(*Result.ObligationType);
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
      // A generated proof is reported only if it is not a proof.
      if (D.Quiet && (D.K == VerifyDiagnostic::Verified ||
                      D.K == VerifyDiagnostic::Certified ||
                      D.K == VerifyDiagnostic::Exported))
        continue;
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
        if (D.Result)
          for (const QuantifierProfileEntry &Entry : D.Result->QuantifierProfile)
            OS << "note: the quantifier at " << Entry.Line << ":"
               << Entry.Column << " was instantiated " << Entry.Instances
               << " times, up to generation " << Entry.MaxGeneration << "\n";
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
      case VerifyDiagnostic::MixedProof:
        OS << "Proved (" << D.Result->BackendName << "): " << D.Message << "\n";
        break;
      case VerifyDiagnostic::Trusted:
        OS << "Trusted: " << D.Message << "\n";
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