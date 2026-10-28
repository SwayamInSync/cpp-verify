//===--- Main.cpp - cpp-verify standalone tool ----------------------------===//
#include "../../lib/Verify/Backend/CVC5Backend.h"
#include "../../lib/Verify/Backend/ObligationSerialization.h"
#include "../../lib/Verify/Backend/ObligationSimplify.h"
#include "../../lib/Verify/Backend/ProofCache.h"
#include "../../lib/Verify/Backend/VerifyBackend.h"
#include "Counterexample.h"
#include "CppVerifyVersion.h"
#include "DumpIR.h"
#include "StructuredOutput.h"
#include "Verifier.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ASTContext.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/CompilerInvocation.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Frontend/TextDiagnosticPrinter.h"
#include "clang/Lex/Lexer.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/FormatVariadic.h"
#include "llvm/Support/InitLLVM.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/Process.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/raw_ostream.h"
#include <chrono>
#include <cstdlib>
#include <limits>
#if defined(__GLIBC__)
#include <malloc.h>
#endif

using namespace clang;
using namespace clang::tooling;
using namespace llvm;

static cl::OptionCategory CppVerifyCategory("cpp-verify options");
static cl::extrahelp CommonHelp(CommonOptionsParser::HelpMessage);
static cl::opt<std::string>
    DumpIR("dump-ir",
           cl::desc("Dump verification IR (layers: 1=vcr 2=passive 3=vc 4=z3; "
                    "comma-separated, default all)"),
           cl::value_desc("layers"), cl::ValueOptional,
           cl::cat(CppVerifyCategory));

static cl::opt<bool> LowerOnly(
    "lower-only",
    cl::desc("Run through backend encoding without checking satisfiability"),
    cl::init(false), cl::cat(CppVerifyCategory));

static cl::opt<std::string> BackendOpt(
    "backend",
    cl::desc("Verification backend: z3 (default), cvc5, portfolio (z3 and "
             "cvc5 must agree), race (z3 and cvc5 at once, the first proof or "
             "certified counterexample stands), lean, bmc"),
    cl::value_desc("name"), cl::init("z3"), cl::cat(CppVerifyCategory));

static cl::opt<std::string>
    CVC5Path("cvc5-path",
             cl::desc("cvc5 executable for --backend=cvc5, portfolio, or race"),
             cl::value_desc("file"), cl::cat(CppVerifyCategory));

static cl::opt<std::string>
    LeanOut("lean-out",
            cl::desc("Output path for --backend=lean standalone export"),
            cl::value_desc("file"), cl::cat(CppVerifyCategory));

static cl::opt<std::string> LeanProject(
    "lean-project",
    cl::desc("Generate an editable pinned Lean project in this directory"),
    cl::value_desc("directory"), cl::cat(CppVerifyCategory));

static cl::opt<std::string> LeanFallback(
    "lean-fallback",
    cl::desc("Export unresolved Z3 or portfolio obligations to a Lean project"),
    cl::value_desc("directory"), cl::cat(CppVerifyCategory));

static cl::opt<verify::LeanFallbackScope> LeanFallbackScope(
    "lean-fallback-scope",
    cl::desc("Obligations of an unresolved function that --lean-fallback "
             "exports"),
    cl::values(clEnumValN(verify::LeanFallbackScope::Unproved, "unproved",
                          "Only those the solver did not prove (default)"),
               clEnumValN(verify::LeanFallbackScope::All, "all",
                          "Every obligation of the function")),
    cl::init(verify::LeanFallbackScope::Unproved), cl::cat(CppVerifyCategory));

static cl::opt<bool> LeanCertify(
    "lean-certify",
    cl::desc("Kernel-check every proof in --lean-project without admissions"),
    cl::init(false), cl::cat(CppVerifyCategory));

static cl::opt<bool> LeanPruneStale(
    "lean-prune-stale",
    cl::desc("Delete the proofs a Lean project keeps in Stale/ because no "
             "goal has their statement"),
    cl::init(false), cl::cat(CppVerifyCategory));

static cl::opt<bool>
    NoLeanAuto("no-lean-auto",
               cl::desc("Write a stub for each new Lean goal without trying "
                        "cppverify_auto on it"),
               cl::init(false), cl::cat(CppVerifyCategory));

static cl::opt<unsigned> LeanAutoTimeout(
    "lean-auto-timeout",
    cl::desc("Wall-clock milliseconds cppverify_auto may spend on one new "
             "Lean goal (0 = no limit)"),
    cl::init(verify::DefaultLeanAutoTimeoutMs), cl::cat(CppVerifyCategory));

static cl::opt<unsigned>
    BMCUnroll("unroll", cl::desc("Maximum loop unroll bound for --backend=bmc"),
              cl::init(10), cl::cat(CppVerifyCategory));

static const std::string SolverTimeoutDescription =
    "Per-query solver timeout in milliseconds (default " +
    std::to_string(verify::DefaultSolverTimeoutMs) +
    ", 0 = no limit). A query that exceeds it is reported as unresolved "
    "instead of hanging";
static cl::opt<unsigned> SolverTimeout("timeout",
                                       cl::desc(SolverTimeoutDescription),
                                       cl::init(verify::DefaultSolverTimeoutMs),
                                       cl::cat(CppVerifyCategory));

static cl::opt<unsigned> CollectionTimeout(
    "collection-timeout",
    cl::desc("Per-query solver timeout in milliseconds for queries over "
             "sequences, sets, multisets, or maps (default: twice --timeout; "
             "0 = no limit)"),
    cl::cat(CppVerifyCategory));

static cl::opt<unsigned> CertifyTimeout(
    "certify-timeout",
    cl::desc("Milliseconds the check of one counterexample against the "
             "definitions may take, so that one slow model leaves the query "
             "time to others (default: half of the query timeout; 0 = the "
             "query's own time)"),
    cl::cat(CppVerifyCategory));

static std::optional<unsigned> certifyTimeoutMs() {
  if (CertifyTimeout.getNumOccurrences())
    return CertifyTimeout.getValue();
  return std::nullopt;
}

static cl::opt<unsigned> FunctionTimeout(
    "function-timeout",
    cl::desc("Milliseconds all queries of one function may take together "
             "(default: ten times --timeout; 0 = no limit)"),
    cl::cat(CppVerifyCategory));

static unsigned functionTimeoutMs() {
  if (FunctionTimeout.getNumOccurrences())
    return FunctionTimeout;
  return SolverTimeout > std::numeric_limits<unsigned>::max() / 10
             ? 0
             : 10 * SolverTimeout;
}

static unsigned collectionTimeoutMs() {
  if (CollectionTimeout.getNumOccurrences())
    return CollectionTimeout;
  return SolverTimeout > std::numeric_limits<unsigned>::max() / 2
             ? 0
             : 2 * SolverTimeout;
}

static cl::opt<unsigned> SolverResourceLimit(
    "solver-rlimit",
    cl::desc("Per-query deterministic solver resource limit (0 = no limit)"),
    cl::init(0), cl::cat(CppVerifyCategory));

static cl::opt<unsigned>
    Jobs("jobs",
         cl::desc("Solver workers shared by every function and obligation "
                  "(0 = available physical cores, the default; the "
                  "CPPVERIFY_JOBS environment variable sets the default)"),
         cl::init(0), cl::cat(CppVerifyCategory));

/// --jobs, else one for Lean, which is serial, else CPPVERIFY_JOBS, else
/// every core.
static unsigned jobs() {
  if (Jobs.getNumOccurrences())
    return Jobs;
  if (BackendOpt == "lean")
    return 1;
  unsigned FromEnvironment = 0;
  if (std::optional<std::string> Value =
          llvm::sys::Process::GetEnv("CPPVERIFY_JOBS"))
    if (!llvm::StringRef(*Value).getAsInteger(10, FromEnvironment))
      return FromEnvironment;
  return 0;
}

static const std::string MaxQueryNodesDescription =
    "Maximum expression nodes of one function's proof obligations, checked "
    "as they are built (default " +
    std::to_string(verify::DefaultMaxQueryNodes) + "; 0 = no limit)";

static cl::opt<uint64_t> MaxQueryNodes(
    "max-query-nodes", cl::desc(MaxQueryNodesDescription),
    cl::init(verify::DefaultMaxQueryNodes), cl::cat(CppVerifyCategory));

static cl::opt<uint64_t> MemoryLimit(
    "memory-limit",
    cl::desc("Megabytes Z3's queries may allocate together, and each cvc5 "
             "process (default 8192; 0 = no limit)"),
    cl::init(verify::DefaultMemoryLimitMB), cl::cat(CppVerifyCategory));

static cl::opt<verify::MachineIntegerEncoding> IntEncoding(
    "int-encoding",
    cl::desc("Solver encoding of C++ machine integers (all are exact)"),
    cl::values(clEnumValN(verify::MachineIntegerEncoding::Auto, "auto",
                          "Integers, or bit-vectors for a query that needs "
                          "bit-level operations (default)"),
               clEnumValN(verify::MachineIntegerEncoding::Integer, "integer",
                          "Integers reduced modulo 2^w"),
               clEnumValN(verify::MachineIntegerEncoding::BitVector,
                          "bitvector", "Solver bit-vectors")),
    cl::init(verify::MachineIntegerEncoding::Auto), cl::cat(CppVerifyCategory));

static cl::opt<std::string> ProofCache(
    "proof-cache",
    cl::desc("Cache successful dependency-scoped proofs in this directory"),
    cl::value_desc("directory"), cl::cat(CppVerifyCategory));

static cl::opt<uint64_t> ProofCacheMaxMB(
    "proof-cache-max-mb",
    cl::desc("Maximum proof-cache size in MiB (0 = no byte limit)"),
    cl::init(1024), cl::cat(CppVerifyCategory));

static cl::opt<uint64_t> ProofCacheMaxEntries(
    "proof-cache-max-entries",
    cl::desc("Maximum proof-cache entries (0 = no entry limit)"),
    cl::init(100000), cl::cat(CppVerifyCategory));

static cl::opt<bool> CheckUB(
    "check-ub",
    cl::desc("Check memory accesses and pointer arithmetic against the "
             "objects they may address (the default)"),
    cl::init(true), cl::cat(CppVerifyCategory));

static cl::opt<bool> NoCheckUB(
    "no-check-ub",
    cl::desc("Do not check memory accesses against objects; only the "
             "always-on expression definedness checks remain"),
    cl::init(false), cl::cat(CppVerifyCategory));

static cl::opt<bool> ProfileQuantifiers(
    "profile-quantifiers",
    cl::desc("For an unresolved Z3 query, rerun it counting each "
             "quantifier's instantiations and report the busiest, to find "
             "matching loops and poor triggers"),
    cl::init(false), cl::cat(CppVerifyCategory));

static cl::opt<std::string> ObligationOut(
    "obligation-out",
    cl::desc("Write versioned backend-neutral obligation modules to this file"),
    cl::value_desc("file"), cl::cat(CppVerifyCategory));

static cl::opt<std::string> ObligationIn(
    "obligation-in",
    cl::desc("Validate and replay a backend-neutral obligation archive"),
    cl::value_desc("file"), cl::cat(CppVerifyCategory));

enum class OutputFormat { Text, Json, Sarif, GitHub };

static cl::opt<OutputFormat> DiagnosticsFormat(
    "diagnostics-format", cl::desc("Format of results and diagnostics"),
    cl::values(
        clEnumValN(OutputFormat::Text, "text", "Human-readable text (default)"),
        clEnumValN(OutputFormat::Json, "json",
                   "JSON Lines (cppverify.diagnostic/2), ending with a "
                   "summary record"),
        clEnumValN(OutputFormat::Sarif, "sarif",
                   "One SARIF 2.1.0 log at the end of the run"),
        clEnumValN(OutputFormat::GitHub, "github",
                   "Text, with a GitHub workflow annotation for each error and "
                   "warning")),
    cl::init(OutputFormat::Text), cl::cat(CppVerifyCategory));

/// Whether results are records: JSON Lines, or the SARIF made of them.
static bool structuredOutput() {
  return DiagnosticsFormat == OutputFormat::Json ||
         DiagnosticsFormat == OutputFormat::Sarif;
}

static verify::DiagnosticFormat verifierFormat() {
  switch (DiagnosticsFormat) {
  case OutputFormat::Text:
    return verify::DiagnosticFormat::Text;
  case OutputFormat::Json:
  case OutputFormat::Sarif:
    return verify::DiagnosticFormat::Json;
  case OutputFormat::GitHub:
    return verify::DiagnosticFormat::GitHub;
  }
  return verify::DiagnosticFormat::Text;
}

// In SARIF mode the records are collected here and translated at the end.
static std::string gRecords;
static llvm::raw_string_ostream gRecordStream(gRecords);

/// Where results go: standard output, or the records of a SARIF log.
static llvm::raw_ostream &out() {
  if (DiagnosticsFormat == OutputFormat::Sarif)
    return gRecordStream;
  return llvm::outs();
}

static cl::opt<bool>
    Quiet("quiet",
          cl::desc("Print only what is not a proof (failures, unresolved "
                   "results, errors, warnings) and the summary"),
          cl::cat(CppVerifyCategory));

static cl::opt<bool>
    Verbose("verbose",
            cl::desc("Also print each spec function that needs no check "
                     "(spec axiom)"),
            cl::cat(CppVerifyCategory));

static cl::opt<unsigned> ConfirmBound(
    "confirm-bound",
    cl::desc("For a failure whose counterexample passes through a loop, "
             "unroll each loop up to this many iterations to look for an "
             "execution that fails (default 10, 0 = do not look)"),
    cl::init(10), cl::cat(CppVerifyCategory));

static cl::opt<unsigned> MaxFailures(
    "max-failures",
    cl::desc("Report up to this many failing checks of a function, each with "
             "its own counterexample (default 1, 0 = all; --backend=z3)"),
    cl::init(1), cl::cat(CppVerifyCategory));

static cl::list<std::string> FunctionPatterns(
    "function",
    cl::desc("Report only the functions whose names match this glob pattern "
             "(repeatable); what their verdicts rely on is verified too"),
    cl::value_desc("pattern"), cl::cat(CppVerifyCategory));

static cl::opt<bool> ListFunctions(
    "list-functions",
    cl::desc("List the functions a run would verify, with their kinds and "
             "locations, and verify none"),
    cl::cat(CppVerifyCategory));

static cl::opt<std::string> ContractsOut(
    "contracts-out",
    cl::desc("Write the contracts the file verifies and those it assumes from "
             "other files, for --check-contracts"),
    cl::value_desc("file"), cl::cat(CppVerifyCategory));

static cl::opt<bool> CheckContracts(
    "check-contracts",
    cl::desc("Check that the contracts the given records (--contracts-out, "
             "-fverify-contracts-out) assume are established by the "
             "verification of their definitions in others"),
    cl::cat(CppVerifyCategory));

static cl::opt<bool> TimeReport(
    "time-report",
    cl::desc("Report where the run and each function spent their time: "
             "lowering, solving, induction, certification, confirmation"),
    cl::cat(CppVerifyCategory));

static cl::opt<cl::boolOrDefault> Progress(
    "progress",
    cl::desc("Show on standard error how many functions are done (default: "
             "when standard error is a terminal)"),
    cl::cat(CppVerifyCategory));

namespace {

static int gVerifyFailures = 0;
static verify::VerifySummary gSummary;
/// A run over several files settles the contracts each declares without a
/// definition against those the others verify, before printing.
static std::unique_ptr<verify::CrossFileRun> gCrossFile;

/// One line for the run: how many verdicts of each kind it reported, the
/// reasons of the unresolved ones, and the time it took.
static void printSummary(std::chrono::steady_clock::time_point Start) {
  std::vector<std::string> Parts;
  auto add = [&](unsigned N, llvm::StringRef What) {
    if (N)
      Parts.push_back(std::to_string(N) + " " + What.str());
  };
  add(gSummary.Verified, "verified");
  add(gSummary.Failed, "failed");
  if (gSummary.Unresolved) {
    std::vector<std::string> Reasons;
    for (const auto &[Reason, N] : gSummary.Reasons)
      Reasons.push_back(Reason + " " + std::to_string(N));
    Parts.push_back(std::to_string(gSummary.Unresolved) + " unresolved (" +
                    llvm::join(Reasons, ", ") + ")");
  }
  add(gSummary.BoundedSafe, "bounded-safe");
  add(gSummary.Trusted, "trusted");
  add(gSummary.Lowered, "lowered");
  add(gSummary.Exported, "exported");
  add(gSummary.Interrupted, "interrupted");
  const double Seconds =
      std::chrono::duration<double>(std::chrono::steady_clock::now() - Start)
          .count();
  llvm::outs() << "Summary: "
               << (Parts.empty() ? std::string("no verdicts")
                                 : llvm::join(Parts, ", "))
               << llvm::formatv(" in {0:f1} s", Seconds) << "\n";
}
/// The summary as a record: the counts of the text line, by name. It has no
/// time, so that records do not depend on the run; --time-report gives it.
static void printSummaryRecord() {
  llvm::json::Object Record;
  Record["schema"] = verify::SummarySchema;
  Record["verified"] = gSummary.Verified;
  Record["failed"] = gSummary.Failed;
  Record["unresolved"] = gSummary.Unresolved;
  llvm::json::Object Reasons;
  for (const auto &[Reason, N] : gSummary.Reasons)
    Reasons[Reason] = N;
  Record["reasons"] = std::move(Reasons);
  Record["bounded_safe"] = gSummary.BoundedSafe;
  Record["trusted"] = gSummary.Trusted;
  Record["lowered"] = gSummary.Lowered;
  Record["exported"] = gSummary.Exported;
  Record["interrupted"] = gSummary.Interrupted;
  out() << llvm::formatv("{0}\n", llvm::json::Value(std::move(Record)));
}

static std::vector<std::string> gArguments;

/// Ends the run's output: in SARIF mode, the log of the records collected.
static int finishOutput(int ExitCode) {
  if (DiagnosticsFormat != OutputFormat::Sarif)
    return ExitCode;
  gRecordStream.flush();
  std::vector<llvm::json::Value> Records;
  for (llvm::StringRef Line : llvm::split(gRecords, '\n')) {
    if (Line.trim().empty())
      continue;
    if (llvm::Expected<llvm::json::Value> Record = llvm::json::parse(Line))
      Records.push_back(std::move(*Record));
    else
      llvm::consumeError(Record.takeError());
  }
  verify::SarifInvocation Invocation;
  Invocation.Version = verify::releaseVersion().str();
  Invocation.Arguments = gArguments;
  Invocation.ExitCode = ExitCode;
  llvm::outs() << llvm::formatv("{0:2}\n",
                                verify::sarifLog(Records, Invocation));
  return ExitCode;
}

static llvm::raw_ostream *gObligationOut = nullptr;

static uint64_t proofCacheMaxBytes() {
  constexpr uint64_t MiB = 1024ULL * 1024ULL;
  return ProofCacheMaxMB > std::numeric_limits<uint64_t>::max() / MiB
             ? std::numeric_limits<uint64_t>::max()
             : ProofCacheMaxMB * MiB;
}

static verify::BackendExecutionOptions backendExecutionOptions() {
  verify::BackendExecutionOptions Options;
  Options.SolverTimeoutMs = SolverTimeout;
  Options.CollectionTimeoutMs = collectionTimeoutMs();
  Options.CertifyTimeoutMs = certifyTimeoutMs();
  Options.SolverResourceLimit = SolverResourceLimit;
  Options.Jobs = jobs();
  Options.MaxQueryNodes = MaxQueryNodes;
  Options.MemoryLimitMB = MemoryLimit;
  Options.IntegerEncoding = IntEncoding;
  Options.CVC5Path = CVC5Path;
  Options.ProofCachePath = ProofCache;
  Options.ProofCacheMaxBytes = proofCacheMaxBytes();
  Options.ProofCacheMaxEntries = ProofCacheMaxEntries;
  return Options;
}

static verify::VerifyResult
lowerForBackend(const verify::ObligationModule &Module,
                verify::BackendKind Kind, llvm::raw_ostream *Z3Out = nullptr) {
  verify::BackendExecutionOptions Execution = backendExecutionOptions();
  if (Kind == verify::BackendKind::CVC5)
    return verify::lowerSMTLibModule(Module, nullptr, Execution);
  if (Kind == verify::BackendKind::Portfolio ||
      Kind == verify::BackendKind::Race) {
    const std::string Name =
        Kind == verify::BackendKind::Race ? "race" : "portfolio";
    verify::VerifyResult Z3Result =
        verify::lowerObligationModule(Module, Z3Out, Execution);
    if (Z3Result.Status != verify::VerifyStatus::Lowered) {
      Z3Result.BackendName = Name;
      Z3Result.Message =
          "z3 component" +
          (Z3Result.Message.empty() ? std::string() : ": " + Z3Result.Message);
      return Z3Result;
    }
    verify::VerifyResult CVC5Result =
        verify::lowerSMTLibModule(Module, nullptr, Execution);
    if (CVC5Result.Status != verify::VerifyStatus::Lowered) {
      CVC5Result.BackendName = Name;
      CVC5Result.Message = "cvc5 component" + (CVC5Result.Message.empty()
                                                   ? std::string()
                                                   : ": " + CVC5Result.Message);
      return CVC5Result;
    }
    verify::VerifyResult Result;
    Result.Status = verify::VerifyStatus::Lowered;
    Result.BackendName = Name;
    return Result;
  }
  return verify::lowerObligationModule(Module, Z3Out, Execution);
}

// The options of Lean output and Lean projects, which source verification
// and archive replay share.
static void setLeanOptions(verify::VerifyOptions &VOpts) {
  VOpts.LeanOutPath = LeanOut.getValue();
  VOpts.LeanProjectPath = LeanProject.getValue();
  VOpts.LeanFallbackProjectPath = LeanFallback.getValue();
  VOpts.LeanScope = LeanFallbackScope.getValue();
  VOpts.LeanCertify = LeanCertify.getValue();
  VOpts.LeanPruneStale = LeanPruneStale.getValue();
  VOpts.LeanAuto = !NoLeanAuto.getValue();
  VOpts.LeanAutoTimeoutMs = LeanAutoTimeout.getValue();
  VOpts.LeanJobs = Jobs.getNumOccurrences() ? Jobs.getValue() : 0;
}

static void flushFrontendRecords();

class VerifyConsumer : public ASTConsumer {
public:
  void HandleTranslationUnit(ASTContext &Ctx) override {
    // The compiler's records come before the verifier's.
    flushFrontendRecords();
    if (!Ctx.getDiagnostics().getClient()->getNumErrors()) {
      verify::VerifyOptions VOpts;
      if (DumpIR.getNumOccurrences() > 0)
        VOpts.DumpIRLayers = verify::parseDumpIRLayers(DumpIR.getValue());
      VOpts.LowerOnly = LowerOnly.getValue();
      llvm::StringRef B = BackendOpt.getValue();
      if (B == "lean")
        VOpts.Backend = verify::BackendKind::Lean;
      else if (B == "bmc")
        VOpts.Backend = verify::BackendKind::BMC;
      else if (B == "cvc5")
        VOpts.Backend = verify::BackendKind::CVC5;
      else if (B == "portfolio")
        VOpts.Backend = verify::BackendKind::Portfolio;
      else if (B == "race")
        VOpts.Backend = verify::BackendKind::Race;
      else
        VOpts.Backend = verify::BackendKind::Z3;
      setLeanOptions(VOpts);
      VOpts.BMCUnroll = BMCUnroll.getValue();
      VOpts.SolverTimeoutMs = SolverTimeout.getValue();
      VOpts.CollectionTimeoutMs = collectionTimeoutMs();
      VOpts.CertifyTimeoutMs = certifyTimeoutMs();
      VOpts.FunctionTimeoutMs = functionTimeoutMs();
      VOpts.SolverResourceLimit = SolverResourceLimit.getValue();
      // Lean exports one function at a time; --jobs sets its Lean processes.
      VOpts.Jobs = VOpts.Backend == verify::BackendKind::Lean ? 1 : jobs();
      VOpts.MaxQueryNodes = MaxQueryNodes.getValue();
      VOpts.MemoryLimitMB = MemoryLimit.getValue();
      VOpts.IntegerEncoding = IntEncoding.getValue();
      VOpts.CVC5Path = CVC5Path.getValue();
      VOpts.ProofCachePath = ProofCache.getValue();
      VOpts.ProofCacheMaxBytes = proofCacheMaxBytes();
      VOpts.ProofCacheMaxEntries = ProofCacheMaxEntries.getValue();
      VOpts.CheckUB = CheckUB.getValue() && !NoCheckUB.getValue();
      VOpts.ProfileQuantifiers = ProfileQuantifiers.getValue();
      VOpts.Diagnostics = verifierFormat();
      VOpts.ObligationOut = gObligationOut;
      VOpts.Quiet = Quiet.getValue();
      VOpts.Verbose = Verbose.getValue();
      VOpts.ListFunctions = ListFunctions.getValue();
      VOpts.TimeReport = TimeReport.getValue();
      VOpts.ContractsOut = ContractsOut.getValue();
      if (Progress != cl::boolOrDefault::BOU_UNSET)
        VOpts.Progress = Progress == cl::boolOrDefault::BOU_TRUE;
      VOpts.MaxFailures = MaxFailures.getValue();
      VOpts.FunctionPatterns.assign(FunctionPatterns.begin(),
                                    FunctionPatterns.end());
      VOpts.ConfirmBound = ConfirmBound.getValue();
      VOpts.Summary = &gSummary;
      VOpts.CrossFile = gCrossFile.get();
      if (!verify::verifyTranslationUnit(Ctx, out(), VOpts))
        ++gVerifyFailures;
    }
  }
};

class VerifyAction : public ASTFrontendAction {
public:
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI,
                                                 StringRef) override {
    CI.getLangOpts().VerifyContracts = true;
    return std::make_unique<VerifyConsumer>();
  }
};

/// The compiler's diagnostics as the run's format takes them: records of
/// status "frontend" in JSON and SARIF, each with the notes that follow it as
/// related locations; and in GitHub mode the text, with an annotation after
/// each error and warning.
class StructuredDiagnostics : public DiagnosticConsumer {
public:
  explicit StructuredDiagnostics(DiagnosticConsumer *Text) : Text(Text) {}
  ~StructuredDiagnostics() override { flush(); }

  void BeginSourceFile(const LangOptions &LangOpts,
                       const Preprocessor *PP) override {
    if (Text)
      Text->BeginSourceFile(LangOpts, PP);
  }
  void EndSourceFile() override {
    flush();
    if (Text)
      Text->EndSourceFile();
  }
  /// Writes the record still waiting for its notes.
  void finish() { flush(); }

  void HandleDiagnostic(DiagnosticsEngine::Level Level,
                        const Diagnostic &Info) override {
    DiagnosticConsumer::HandleDiagnostic(Level, Info);
    if (Level == DiagnosticsEngine::Ignored)
      return;
    llvm::SmallString<256> Message;
    Info.FormatDiagnostic(Message);
    verify::ObligationSource Source = sourceOf(Info);
    if (Text) {
      Text->HandleDiagnostic(Level, Info);
      if (Level >= DiagnosticsEngine::Warning)
        llvm::outs() << verify::githubCommand(
            Level == DiagnosticsEngine::Warning ? "warning" : "error", Source,
            "clang", Message);
      return;
    }
    if (Level == DiagnosticsEngine::Note && Pending) {
      llvm::json::Object Note;
      Note["message"] = verify::jsonText(Message);
      if (Source.isValid())
        Note["source"] = verify::sourceJSON(Source);
      Related.push_back(std::move(Note));
      return;
    }
    flush();
    llvm::json::Object Record;
    Record["schema"] = verify::DiagnosticSchema;
    Record["status"] = "frontend";
    Record["severity"] = Level == DiagnosticsEngine::Remark    ? "remark"
                         : Level == DiagnosticsEngine::Note    ? "note"
                         : Level == DiagnosticsEngine::Warning ? "warning"
                                                               : "error";
    Record["message"] = verify::jsonText(Message);
    llvm::StringRef Option =
        Info.getDiags()->getDiagnosticIDs()->getWarningOptionForDiag(
            Info.getID());
    if (!Option.empty())
      Record["option"] = ("-W" + Option).str();
    if (Source.isValid())
      Record["source"] = verify::sourceJSON(Source);
    Pending = std::move(Record);
  }

private:
  void flush() {
    if (!Pending)
      return;
    if (!Related.empty())
      (*Pending)["related"] = std::move(Related);
    out() << llvm::formatv("{0}\n", llvm::json::Value(std::move(*Pending)));
    Pending.reset();
    Related = llvm::json::Array();
  }

  /// The diagnostic's source: its location, through its first range.
  static verify::ObligationSource sourceOf(const Diagnostic &Info) {
    verify::ObligationSource Source;
    if (!Info.hasSourceManager() || Info.getLocation().isInvalid())
      return Source;
    const SourceManager &SM = Info.getSourceManager();
    PresumedLoc At = SM.getPresumedLoc(Info.getLocation());
    if (!At.isValid())
      return Source;
    Source.File = At.getFilename();
    Source.Line = Source.EndLine = At.getLine();
    Source.Column = Source.EndColumn = At.getColumn();
    if (Info.getNumRanges() == 0)
      return Source;
    CharSourceRange Range = Info.getRange(0);
    SourceLocation Begin = SM.getExpansionLoc(Range.getBegin());
    SourceLocation End = SM.getExpansionLoc(Range.getEnd());
    if (Range.isTokenRange())
      End = Lexer::getLocForEndOfToken(End, 0, SM, LangOptions());
    PresumedLoc First = SM.getPresumedLoc(Begin);
    PresumedLoc Last = SM.getPresumedLoc(End);
    if (First.isValid() && Last.isValid() &&
        llvm::StringRef(First.getFilename()) == Source.File &&
        llvm::StringRef(Last.getFilename()) == Source.File) {
      if (First.getLine() < Source.Line ||
          (First.getLine() == Source.Line &&
           First.getColumn() < Source.Column)) {
        Source.BeginLine = First.getLine();
        Source.BeginColumn = First.getColumn();
      }
      if (Last.getLine() > Source.Line ||
          (Last.getLine() == Source.Line && Last.getColumn() > Source.Column)) {
        Source.EndLine = Last.getLine();
        Source.EndColumn = Last.getColumn();
      }
    }
    return Source;
  }

  DiagnosticConsumer *Text;
  std::optional<llvm::json::Object> Pending;
  llvm::json::Array Related;
};

static StructuredDiagnostics *gStructured = nullptr;

static void flushFrontendRecords() {
  if (gStructured)
    gStructured->finish();
}

/// Verifies each file whose command line clang accepts. An argument error
/// stops the file, as it stops clang; tooling would print it and go on.
/// Files report to Files when it is set, else with their own options.
class VerifyActionFactory : public FrontendActionFactory {
public:
  VerifyActionFactory(const DiagnosticConsumer &Arguments,
                      DiagnosticConsumer *Files)
      : Arguments(Arguments), Files(Files) {}
  std::unique_ptr<FrontendAction> create() override {
    return std::make_unique<VerifyAction>();
  }
  bool runInvocation(std::shared_ptr<CompilerInvocation> Invocation,
                     FileManager *Files,
                     std::shared_ptr<PCHContainerOperations> PCHContainerOps,
                     DiagnosticConsumer *) override {
    // After Ctrl-C the files left are not read.
    if (verify::interruptRequested())
      return true;
    if (Arguments.getNumErrors() != ArgumentErrors) {
      ArgumentErrors = Arguments.getNumErrors();
      return false;
    }
    return FrontendActionFactory::runInvocation(
        std::move(Invocation), Files, std::move(PCHContainerOps), this->Files);
  }

private:
  const DiagnosticConsumer &Arguments;
  DiagnosticConsumer *Files;
  unsigned ArgumentErrors = 0;
};

// Replay proves each module alone: the contracts and spec facts its proof
// rests on, its qualifiers, and its vacuity belong to the source run.
static constexpr const char ReplayProofNote[] =
    "dependencies not checked in replay";

static llvm::StringRef replayStatusCode(verify::VerifyStatus Status) {
  switch (Status) {
  case verify::VerifyStatus::Lowered:
    return "lowered";
  case verify::VerifyStatus::Verified:
    return "proved-obligations";
  case verify::VerifyStatus::Failed:
    return "failed";
  case verify::VerifyStatus::Unresolved:
    return "unresolved";
  case verify::VerifyStatus::BoundedSafe:
    return "bounded-safe";
  case verify::VerifyStatus::Exported:
    return "exported";
  case verify::VerifyStatus::Certified:
    return "certified";
  case verify::VerifyStatus::MixedProof:
    return "mixed-proof";
  }
  return "unresolved";
}

using verify::jsonText;
using verify::sourceJSON;

static void printReplayJSON(const verify::ObligationModule &Module,
                            const verify::VerifyResult &Result,
                            llvm::StringRef SemanticHash,
                            unsigned LeanAutomatic) {
  llvm::json::Object Record;
  Record["schema"] = verify::DiagnosticSchema;
  Record["status"] = replayStatusCode(Result.Status);
  Record["severity"] = Result.Status == verify::VerifyStatus::BoundedSafe
                           ? "warning"
                       : Result.Status == verify::VerifyStatus::Failed ||
                               Result.Status == verify::VerifyStatus::Unresolved
                           ? "error"
                           : "note";
  Record["function"] = jsonText(Module.FunctionName);
  std::string Message = Result.Message;
  if (Result.Status == verify::VerifyStatus::Verified) {
    Message = ReplayProofNote;
  } else if (Result.Status == verify::VerifyStatus::Failed) {
    Message = "verification failed: " + Module.FunctionName;
    if (Result.ObligationType)
      Message += std::string(" [") +
                 verify::obligationKindName(*Result.ObligationType) + "]";
    if (!Result.Message.empty())
      Message += " (" + Result.Message + ")";
    if (std::string Values = verify::counterexampleText(Result);
        !Values.empty())
      Record["counterexample"] = jsonText(Values);
  }
  Record["message"] = jsonText(Message);
  Record["semantic_hash"] = ("sha256:" + SemanticHash).str();
  if (!Result.BackendName.empty())
    Record["backend"] = Result.BackendName;
  if (Result.Reason != verify::VerifyReason::None)
    Record["reason"] = verify::verifyReasonCode(Result.Reason);
  if (Result.Bound)
    Record["bound"] = static_cast<int64_t>(*Result.Bound);
  if (Result.Status == verify::VerifyStatus::Exported && LeanAutomatic)
    Record["lean_automatic"] = static_cast<int64_t>(LeanAutomatic);
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
  if (Result.Source.isValid())
    Record["source"] = sourceJSON(Result.Source);
  if (!Result.ObligationId.empty()) {
    llvm::json::Object Obligation;
    Obligation["id"] = jsonText(Result.ObligationId);
    if (Result.ObligationType)
      Obligation["kind"] = verify::obligationKindName(*Result.ObligationType);
    if (Result.Source.isValid())
      Obligation["source"] = sourceJSON(Result.Source);
    Record["obligation"] = std::move(Obligation);
  }
  if (!Result.Model.empty()) {
    llvm::json::Array Model;
    for (const verify::VerifyModelValue &Value : Result.Model) {
      llvm::json::Object Entry;
      Entry["name"] = jsonText(Value.DisplayName);
      Entry["ssa_name"] = jsonText(Value.InternalName);
      Entry["sort"] = verify::formatLogicSort(Value.Sort);
      Entry["value"] = Value.Value ? llvm::json::Value(jsonText(*Value.Value))
                                   : llvm::json::Value(nullptr);
      if (Value.Source.isValid())
        Entry["source"] = sourceJSON(Value.Source);
      if (Value.OnPath == false)
        Entry["on_path"] = false;
      Model.push_back(std::move(Entry));
    }
    Record["model"] = std::move(Model);
  }
  if (!Result.Trace.empty()) {
    llvm::json::Array Trace;
    for (const verify::VerifyTraceEvent &Event : Result.Trace) {
      llvm::json::Object Entry;
      const char *Kind =
          Event.Kind == verify::DiagnosticTraceKind::Call         ? "call"
          : Event.Kind == verify::DiagnosticTraceKind::Loop       ? "loop"
          : Event.Kind == verify::DiagnosticTraceKind::HeapWrite  ? "heap-write"
          : Event.Kind == verify::DiagnosticTraceKind::Allocation ? "allocation"
          : Event.Kind == verify::DiagnosticTraceKind::LifetimeEnd
              ? "lifetime-end"
          : Event.Kind == verify::DiagnosticTraceKind::Deallocation
              ? "deallocation"
          : Event.Kind == verify::DiagnosticTraceKind::Return ? "return"
                                                              : "branch";
      Entry["kind"] = Kind;
      Entry["message"] = jsonText(Event.Message);
      Entry["text"] = jsonText(verify::traceStepText(Event));
      Entry["active"] = Event.Active ? llvm::json::Value(*Event.Active)
                                     : llvm::json::Value(nullptr);
      if (Event.Source.isValid())
        Entry["source"] = sourceJSON(Event.Source);
      llvm::json::Array Values;
      for (const verify::VerifyTraceValue &Value : Event.Values) {
        llvm::json::Object Item;
        Item["label"] = jsonText(Value.Label);
        Item["sort"] = verify::formatLogicSort(Value.Sort);
        Item["value"] = Value.Value ? llvm::json::Value(jsonText(*Value.Value))
                                    : llvm::json::Value(nullptr);
        Values.push_back(std::move(Item));
      }
      if (!Values.empty())
        Entry["values"] = std::move(Values);
      Trace.push_back(std::move(Entry));
    }
    Record["trace"] = std::move(Trace);
  }
  out() << llvm::formatv("{0}\n", llvm::json::Value(std::move(Record)));
}

/// Selects the backend that the only backend an option applies to, when no
/// backend is named, and rejects an option the run would not use.
static bool resolveOptions(bool Replay) {
  auto given = [](const cl::Option &Option) {
    return Option.getNumOccurrences() > 0;
  };
  if (!given(BackendOpt)) {
    if (!LeanOut.empty() || !LeanProject.empty())
      BackendOpt.setValue("lean");
    else if (given(BMCUnroll) && !Replay)
      BackendOpt.setValue("bmc");
  }
  const StringRef Backend = BackendOpt.getValue();
  const cl::Option *SolverOption = nullptr;
  for (const cl::Option *Option : std::initializer_list<const cl::Option *>{
           &SolverTimeout, &CollectionTimeout, &CertifyTimeout,
           &FunctionTimeout, &SolverResourceLimit, &MemoryLimit,
           &IntEncoding})
    if (!SolverOption && given(*Option))
      SolverOption = Option;
  std::string Error;
  if (Backend != "z3" && Backend != "cvc5" && Backend != "portfolio" &&
      Backend != "race" && Backend != "lean" && Backend != "bmc")
    Error = "unknown verification backend '" + Backend.str() +
            "'; expected z3, cvc5, portfolio, race, lean, or bmc";
  else if (!CVC5Path.empty() && Backend != "cvc5" && Backend != "portfolio" &&
           Backend != "race")
    Error = "--cvc5-path requires --backend=cvc5, --backend=portfolio, or "
            "--backend=race";
  else if (given(BMCUnroll) && !Replay && Backend != "bmc")
    Error = "--unroll requires --backend=bmc";
  else if (given(ConfirmBound) &&
           (Replay || Backend == "bmc" || Backend == "lean"))
    Error = "--confirm-bound requires source verification with --backend=z3, "
            "cvc5, portfolio, or race";
  else if (given(MaxFailures) && (Replay || Backend != "z3"))
    Error = "--max-failures requires source verification with --backend=z3";
  else if (given(LeanFallbackScope) && LeanFallback.empty())
    Error = "--lean-fallback-scope requires --lean-fallback";
  else if (given(LeanAutoTimeout) && LeanProject.empty() &&
           LeanFallback.empty())
    Error = "--lean-auto-timeout requires --lean-project or --lean-fallback";
  else if ((given(ProofCacheMaxMB) || given(ProofCacheMaxEntries)) &&
           ProofCache.empty())
    Error = "--proof-cache-max-mb and --proof-cache-max-entries require "
            "--proof-cache";
  else if (ProfileQuantifiers && Replay)
    Error = "--profile-quantifiers applies to source verification, not to "
            "archive replay";
  else if (ProfileQuantifiers && (Backend == "cvc5" || Backend == "lean"))
    Error = "--profile-quantifiers requires a backend that runs Z3: z3, "
            "portfolio, race, or bmc";
  else if (SolverOption && Backend == "lean")
    Error = "--" + SolverOption->ArgStr.str() +
            " requires a backend that runs an SMT solver";
  else if ((given(CheckUB) || given(NoCheckUB)) && Replay)
    Error = "--check-ub and --no-check-ub apply to source verification; an "
            "archive keeps the checks it was written with";
  else if (given(TimeReport) && Replay)
    Error = "--time-report requires source verification";
  if (Error.empty())
    return true;
  llvm::errs() << "error: " << Error << "\n";
  return false;
}

static int replayObligationArchive() {
  if (!ObligationOut.empty()) {
    llvm::errs() << "error: --obligation-in and --obligation-out are mutually "
                    "exclusive\n";
    return 1;
  }
  if (!LeanFallback.empty()) {
    llvm::errs() << "error: --lean-fallback applies to source verification; "
                    "archive replay writes a Lean project with "
                    "--lean-project\n";
    return 1;
  }
  if (LeanProject.empty() && (LeanCertify || LeanPruneStale || NoLeanAuto)) {
    llvm::errs() << "error: --lean-certify, --lean-prune-stale, and "
                    "--no-lean-auto require --lean-project\n";
    return 1;
  }
  if (!LeanProject.empty() && BackendOpt != "lean") {
    llvm::errs() << "error: --lean-project requires --backend=lean\n";
    return 1;
  }
  if (!LeanProject.empty() && (!LeanOut.empty() || LowerOnly)) {
    llvm::errs() << "error: --lean-project cannot be combined with "
                 << (LowerOnly ? "--lower-only" : "--lean-out") << "\n";
    return 1;
  }
  // A project's Lean processes run at once; the scratch-pad is one file.
  if (BackendOpt == "lean" &&
      ((LeanProject.empty() && jobs() != 1) || !ProofCache.empty())) {
    llvm::errs() << "error: --proof-cache is not supported by Lean replay, "
                    "nor --jobs by its scratch-pad\n";
    return 1;
  }
  if (BackendOpt == "cvc5" && !ProofCache.empty()) {
    llvm::errs()
        << "error: --proof-cache is not supported by --backend=cvc5; use "
           "--backend=portfolio to cache its Z3 component\n";
    return 1;
  }
  if (LowerOnly && !ProofCache.empty()) {
    llvm::errs()
        << "error: --proof-cache cannot be combined with --lower-only\n";
    return 1;
  }

  verify::setZ3MemoryLimit(MemoryLimit);
  auto Buffer = llvm::MemoryBuffer::getFile(ObligationIn);
  if (!Buffer) {
    llvm::errs() << "error: cannot read obligation archive: "
                 << Buffer.getError().message() << "\n";
    return 1;
  }
  auto DecodedModules =
      verify::deserializeObligationModules((*Buffer)->getBuffer());
  if (!DecodedModules) {
    llvm::errs() << "error: invalid obligation archive: "
                 << llvm::toString(DecodedModules.takeError()) << "\n";
    return 1;
  }
  if (DecodedModules->empty()) {
    llvm::errs() << "error: obligation archive contains no modules\n";
    return 1;
  }
  std::vector<verify::ObligationModule> Modules;
  Modules.reserve(DecodedModules->size());
  for (verify::ObligationModule &Module : *DecodedModules) {
    auto Simplified = verify::simplifyObligationModule(std::move(Module));
    if (!Simplified) {
      llvm::errs() << "error: cannot canonicalize obligation archive: "
                   << llvm::toString(Simplified.takeError()) << "\n";
      return 1;
    }
    Modules.push_back(std::move(*Simplified));
  }
  for (const verify::ObligationModule &Module : Modules) {
    if (BackendOpt == "bmc" && !Module.BMCTransform) {
      llvm::errs() << "error: BMC cannot replay an untransformed "
                      "backend-neutral archive; bounded unrolling must run "
                      "before obligation lowering\n";
      return 1;
    }
    if ((BackendOpt == "cvc5" || BackendOpt == "portfolio" ||
         BackendOpt == "race") &&
        Module.BMCTransform) {
      llvm::errs() << "error: cvc5, portfolio, and race replay do not yet "
                      "aggregate BMC-transformed archives; use --backend=bmc\n";
      return 1;
    }
    if (!Module.BMCTransform && BMCUnroll.getNumOccurrences() > 0) {
      llvm::errs() << "error: --unroll requires a BMC-transformed archive\n";
      return 1;
    }
    if (Module.BMCTransform && BMCUnroll.getNumOccurrences() > 0 &&
        BMCUnroll != Module.BMCTransform->UnrollBound) {
      llvm::errs() << "error: requested BMC bound " << BMCUnroll
                   << " does not match archived bound "
                   << Module.BMCTransform->UnrollBound << "\n";
      return 1;
    }
  }

  std::unique_ptr<llvm::raw_fd_ostream> LeanFile;
  llvm::raw_ostream *LeanStream = nullptr;
  if (BackendOpt == "lean" && LeanProject.empty()) {
    if (LeanOut.empty()) {
      llvm::errs() << "error: --backend=lean archive replay requires "
                      "--lean-out or --lean-project\n";
      return 1;
    }
    std::error_code EC;
    LeanFile = std::make_unique<llvm::raw_fd_ostream>(LeanOut, EC,
                                                      llvm::sys::fs::OF_Text);
    if (EC) {
      llvm::errs() << "error: cannot open Lean output: " << EC.message()
                   << "\n";
      return 1;
    }
    LeanStream = LeanFile.get();
  } else if (!LeanOut.empty()) {
    llvm::errs() << "error: --lean-out requires --backend=lean\n";
    return 1;
  }

  verify::BackendKind Kind = BackendOpt == "lean"   ? verify::BackendKind::Lean
                             : BackendOpt == "cvc5" ? verify::BackendKind::CVC5
                             : BackendOpt == "portfolio"
                                 ? verify::BackendKind::Portfolio
                             : BackendOpt == "race" ? verify::BackendKind::Race
                             : BackendOpt == "bmc"  ? verify::BackendKind::BMC
                                                    : verify::BackendKind::Z3;
  std::unique_ptr<verify::VerifyBackend> Backend = verify::createVerifyBackend(
      Kind, LeanStream, BMCUnroll, backendExecutionOptions());
  const unsigned DumpLayers = DumpIR.getNumOccurrences() > 0
                                  ? verify::parseDumpIRLayers(DumpIR.getValue())
                                  : 0;
  // A Lean project takes every module before any is certified.
  std::optional<verify::LeanProjectReplay> Project;
  if (!LeanProject.empty() && !verify::interruptRequested()) {
    verify::VerifyOptions VOpts;
    VOpts.Backend = verify::BackendKind::Lean;
    setLeanOptions(VOpts);
    Project = verify::replayLeanProject(Modules, VOpts);
    for (const std::string &Warning : Project->Warnings) {
      if (!structuredOutput()) {
        llvm::outs() << "warning: " << Warning << "\n";
        continue;
      }
      llvm::json::Object Record;
      Record["schema"] = verify::DiagnosticSchema;
      Record["status"] = "warning";
      Record["severity"] = "warning";
      Record["message"] = jsonText(Warning);
      out() << llvm::formatv("{0}\n", llvm::json::Value(std::move(Record)));
    }
    if (!Project->Error.empty()) {
      llvm::errs() << "error: " << Project->Error << "\n";
      return 1;
    }
  }
  bool AllOk = true;
  for (size_t Index = 0; Index != Modules.size(); ++Index) {
    const verify::ObligationModule &Module = Modules[Index];
    if (DumpLayers & verify::LayerVC)
      verify::dumpVC(Module, llvm::outs());

    verify::VerifyResult Result;
    const unsigned LeanAutomatic = Project ? Project->Automatic[Index] : 0;
    if (Project) {
      Result = Project->Results[Index];
    } else if (LowerOnly) {
      Result = lowerForBackend(
          Module, Kind, DumpLayers & verify::LayerZ3 ? &llvm::outs() : nullptr);
    } else if (!verify::interruptRequested()) {
      // Lean exports a bounded module, its bound stated with its goals.
      if (Module.BMCTransform && Kind != verify::BackendKind::Lean) {
        std::unique_ptr<verify::VerifyBackend> BMCBackend =
            verify::createVerifyBackend(verify::BackendKind::BMC, nullptr,
                                        Module.BMCTransform->UnrollBound,
                                        backendExecutionOptions());
        Result = BMCBackend->verify(Module);
      } else {
        Result = Backend->verify(Module);
        if (Module.BMCTransform)
          Result.Bound = Module.BMCTransform->UnrollBound;
      }
    }
    // After Ctrl-C no result is final, whatever the queries returned.
    if (!LowerOnly && verify::interruptRequested()) {
      Result = verify::VerifyResult();
      Result.Status = verify::VerifyStatus::Unresolved;
      Result.Reason = verify::VerifyReason::Interrupted;
    }

    const std::string Hash = verify::obligationSemanticHash(Module);
    if (structuredOutput()) {
      printReplayJSON(Module, Result, Hash, LeanAutomatic);
      if (Result.Status != verify::VerifyStatus::Lowered &&
          Result.Status != verify::VerifyStatus::Verified &&
          Result.Status != verify::VerifyStatus::Exported)
        AllOk = false;
      continue;
    }
    if (Result.Reason == verify::VerifyReason::Interrupted) {
      AllOk = false;
      llvm::outs() << "Interrupted: " << Module.FunctionName << "\n";
      continue;
    }
    std::string Suffix = " [backend=" + Result.BackendName;
    if (Result.Bound)
      Suffix += ", bound=" + std::to_string(*Result.Bound);
    Suffix += "]";
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
    if (Result.Reason != verify::VerifyReason::None)
      Suffix +=
          " [reason=" + verify::verifyReasonCode(Result.Reason).str() + "]";
    Suffix += " [semantic-hash=sha256:" + Hash + "]";
    auto printResultSource = [&]() {
      verify::ObligationSource Source = Result.Source;
      if (!Source.isValid() && !Result.ObligationId.empty()) {
        auto It = llvm::find_if(Module.Obligations,
                                [&](const verify::Obligation &Item) {
                                  return Item.Id == Result.ObligationId ||
                                         Item.StableId == Result.ObligationId;
                                });
        if (It != Module.Obligations.end())
          Source = It->Source;
      }
      if (Source.isValid())
        llvm::outs() << Source.File << ":" << Source.Line << ":"
                     << Source.Column << ": ";
    };
    switch (Result.Status) {
    case verify::VerifyStatus::Lowered:
      llvm::outs() << "Lowered: " << Module.FunctionName << Suffix << "\n";
      break;
    case verify::VerifyStatus::Verified:
      llvm::outs() << "Proved obligations: " << Module.FunctionName << " ("
                   << ReplayProofNote << ")" << Suffix << "\n";
      break;
    case verify::VerifyStatus::Exported:
      llvm::outs() << "Exported: lean obligation: " << Module.FunctionName;
      if (LeanAutomatic)
        llvm::outs() << " (cppverify_auto proved " << LeanAutomatic << " of "
                     << std::set<std::string>(Result.LeanGoals.begin(),
                                              Result.LeanGoals.end())
                            .size()
                     << " goals)";
      llvm::outs() << Suffix << "\n";
      break;
    case verify::VerifyStatus::Failed:
      AllOk = false;
      printResultSource();
      llvm::outs() << "error: verification failed: " << Module.FunctionName;
      if (Result.ObligationType)
        llvm::outs() << " ["
                     << verify::obligationKindName(*Result.ObligationType)
                     << "]";
      else if (!Result.ObligationId.empty())
        llvm::outs() << " [" << Result.ObligationId << "]";
      if (!Result.Message.empty())
        llvm::outs() << " (" << Result.Message << ")";
      llvm::outs() << Suffix << "\n";
      if (std::string Values = verify::counterexampleText(Result);
          !Values.empty())
        llvm::outs() << "note: counterexample: " << Values << "\n";
      for (const verify::VerifyTraceEvent &Event : Result.Trace) {
        if (Event.Source.isValid())
          llvm::outs() << Event.Source.File << ":" << Event.Source.Line << ":"
                       << Event.Source.Column << ": ";
        llvm::outs() << "note: " << verify::traceStepText(Event) << "\n";
      }
      break;
    case verify::VerifyStatus::Unresolved:
      AllOk = false;
      printResultSource();
      llvm::outs() << "Unresolved: " << Module.FunctionName;
      if (!Result.Message.empty())
        llvm::outs() << " (" << Result.Message << ")";
      llvm::outs() << Suffix << "\n";
      break;
    case verify::VerifyStatus::BoundedSafe:
      AllOk = false;
      printResultSource();
      llvm::outs() << "BoundedSafe: " << Module.FunctionName;
      if (!Result.Message.empty())
        llvm::outs() << " (" << Result.Message << ")";
      llvm::outs() << Suffix << "\n";
      break;
    case verify::VerifyStatus::Certified:
    case verify::VerifyStatus::MixedProof:
      AllOk = false;
      llvm::outs() << "Unresolved: " << Module.FunctionName
                   << " (archive backend returned an invalid replay status)"
                   << Suffix << "\n";
      break;
    }
  }
  if (llvm::Error Error = verify::pruneProofCache(
          ProofCache.getValue(), proofCacheMaxBytes(), ProofCacheMaxEntries))
    llvm::errs() << "warning: cannot prune the proof cache: "
                 << llvm::toString(std::move(Error)) << "\n";
  if (LeanFile) {
    LeanFile->flush();
    if (LeanFile->has_error()) {
      llvm::errs() << "error: cannot write Lean output\n";
      return 1;
    }
  }
  if (verify::interruptRequested())
    return 130;
  return AllOk ? 0 : 1;
}

} // namespace

int main(int argc, const char **argv) {
  const auto Start = std::chrono::steady_clock::now();
  llvm::InitLLVM X(argc, argv);
  gArguments.assign(argv, argv + argc);
  // The first Ctrl-C stops the solvers and reports what is not finished; a
  // second one ends the process.
  llvm::sys::SetInterruptFunction(verify::requestInterrupt);
#if defined(__GLIBC__)
  // Each obligation's Z3 context frees about 17 MB. Without padding, glibc
  // returns it to the system when it lies at the top of the heap, and the
  // next context faults every page back in.
  mallopt(M_TOP_PAD, 64 << 20);
#endif

  static const char ReplayPlaceholder[] = "cppverify-obligation-replay.cpp";
  bool HasObligationInput = false;
  for (int I = 1; I < argc; ++I) {
    llvm::StringRef Arg(argv[I]);
    if (Arg == "--obligation-in" || Arg.starts_with("--obligation-in=")) {
      HasObligationInput = true;
      break;
    }
  }
  std::vector<const char *> AdjustedArgv(argv, argv + argc);
  if (HasObligationInput)
    AdjustedArgv.push_back(ReplayPlaceholder);
  // Without "--", Clang tooling looks for a compile_commands.json and reports
  // running "without flags" when there is none. cpp-verify adds its own flags,
  // so it looks for the database itself below, and a file without one is
  // ordinary use.
  const bool ExplicitFlags = llvm::any_of(AdjustedArgv, [](const char *Arg) {
    return llvm::StringRef(Arg) == "--";
  });
  if (!ExplicitFlags)
    AdjustedArgv.push_back("--");
  argv = AdjustedArgv.data();
  argc = static_cast<int>(AdjustedArgv.size());

  cl::SetVersionPrinter([](raw_ostream &OS) { verify::printVersion(OS); });
  auto ExpectedParser =
      CommonOptionsParser::create(argc, argv, CppVerifyCategory);
  if (!ExpectedParser) {
    llvm::errs() << toString(ExpectedParser.takeError()) << "\n";
    return 1;
  }
  CommonOptionsParser &OptionsParser = ExpectedParser.get();
  if (!resolveOptions(!ObligationIn.empty()))
    return 1;
  if (CheckContracts)
    return verify::checkContracts(OptionsParser.getSourcePathList(),
                                  llvm::outs()) != 0;
  if (!ContractsOut.empty() && OptionsParser.getSourcePathList().size() != 1) {
    llvm::errs() << "error: --contracts-out records one file; a run over "
                    "several files settles their contracts itself\n";
    return 1;
  }
  if (!ObligationIn.empty()) {
    const std::vector<std::string> &Sources = OptionsParser.getSourcePathList();
    if (Sources.size() != 1 || Sources.front() != ReplayPlaceholder) {
      llvm::errs() << "error: --obligation-in cannot be combined with C++ "
                      "source files\n";
      return 1;
    }
    return finishOutput(replayObligationArchive());
  }

  std::unique_ptr<llvm::raw_fd_ostream> ObligationFile;
  if (!ObligationOut.empty()) {
    std::error_code EC;
    ObligationFile = std::make_unique<llvm::raw_fd_ostream>(
        ObligationOut, EC, llvm::sys::fs::OF_None);
    if (EC) {
      llvm::errs() << "error: cannot open obligation archive: " << EC.message()
                   << "\n";
      return 1;
    }
    gObligationOut = ObligationFile.get();
  }

  std::unique_ptr<ArgumentsAdjustingCompilations> Database;
  if (!ExplicitFlags) {
    std::string Error;
    llvm::StringRef BuildPath;
    if (auto *Option = cl::getRegisteredOptions().lookup("p"))
      BuildPath = static_cast<cl::opt<std::string> *>(Option)->getValue();
    std::unique_ptr<CompilationDatabase> Found =
        BuildPath.empty()
            ? CompilationDatabase::autoDetectFromSource(
                  OptionsParser.getSourcePathList().front(), Error)
            : CompilationDatabase::autoDetectFromDirectory(BuildPath, Error);
    if (!Found && !BuildPath.empty()) {
      llvm::errs() << "error: -p " << BuildPath
                   << " names no compilation database:\n"
                   << Error;
      return 1;
    }
    if (Found) {
      Database =
          std::make_unique<ArgumentsAdjustingCompilations>(std::move(Found));
      Database->appendArgumentsAdjuster(OptionsParser.getArgumentsAdjuster());
    }
  }
  ClangTool Tool(Database ? *Database : OptionsParser.getCompilations(),
                 OptionsParser.getSourcePathList());
  Tool.appendArgumentsAdjuster(getInsertArgumentAdjuster(
      {"-fverify-contracts", "-std=c++17"}, ArgumentInsertPosition::BEGIN));
  // Clang takes a .h file for C; here every input is C++.
  Tool.appendArgumentsAdjuster(
      [](const CommandLineArguments &Args, StringRef Filename) {
        if (llvm::sys::path::extension(Filename) != ".h")
          return Args;
        CommandLineArguments Adjusted = Args;
        Adjusted.insert(Adjusted.begin() + 1, "-xc++-header");
        return Adjusted;
      });
#if defined(__APPLE__)
  if (const char *SDK = std::getenv("SDKROOT"); SDK && SDK[0])
    Tool.appendArgumentsAdjuster(getInsertArgumentAdjuster(
        {"-isysroot", SDK}, ArgumentInsertPosition::BEGIN));
#endif

  std::unique_ptr<DiagnosticOptions> ArgumentOptions =
      CreateAndPopulateDiagOpts({"cpp-verify"});
  TextDiagnosticPrinter ArgumentDiagnostics(llvm::errs(), *ArgumentOptions);
  // Records and annotations need every file to report to one consumer.
  std::optional<StructuredDiagnostics> Structured;
  if (DiagnosticsFormat != OutputFormat::Text)
    Structured.emplace(DiagnosticsFormat == OutputFormat::GitHub
                           ? &ArgumentDiagnostics
                           : nullptr);
  gStructured = Structured ? &*Structured : nullptr;
  DiagnosticConsumer &Arguments =
      Structured ? static_cast<DiagnosticConsumer &>(*Structured)
                 : ArgumentDiagnostics;
  Tool.setDiagnosticConsumer(&Arguments);
  VerifyActionFactory Factory(Arguments, Structured ? &*Structured : nullptr);
  // Lean exports and --list-functions have no verdicts to settle.
  if (OptionsParser.getSourcePathList().size() > 1 && BackendOpt != "lean" &&
      LeanFallback.empty() && !ListFunctions)
    gCrossFile = std::make_unique<verify::CrossFileRun>();
  int RC = Tool.run(&Factory);
  if (gCrossFile)
    gVerifyFailures += gCrossFile->finish(out(), &gSummary);
  if (Structured)
    Structured->finish();
  gStructured = nullptr;
  if (!ListFunctions) {
    if (structuredOutput())
      printSummaryRecord();
    else
      printSummary(Start);
  }
  if (verify::interruptRequested())
    return finishOutput(130);
  if (RC != 0)
    return finishOutput(RC);
  if (ObligationFile) {
    ObligationFile->flush();
    if (ObligationFile->has_error()) {
      llvm::errs() << "error: cannot write obligation archive\n";
      return finishOutput(1);
    }
  }
  return finishOutput(gVerifyFailures > 0 ? 1 : 0);
}
