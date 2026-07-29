//===--- Main.cpp - cpp-verify standalone tool ----------------------------===//
#include "../../lib/Verify/Backend/ObligationSerialization.h"
#include "../../lib/Verify/Backend/ObligationSimplify.h"
#include "../../lib/Verify/Backend/VerifyBackend.h"
#include "DumpIR.h"
#include "Verifier.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ASTContext.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/FormatVariadic.h"
#include "llvm/Support/InitLLVM.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>
#include <limits>

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
    "backend", cl::desc("Verification backend: z3 (default), lean, bmc"),
    cl::value_desc("name"), cl::init("z3"), cl::cat(CppVerifyCategory));

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
    cl::desc("Export unresolved Z3 obligations to an editable Lean project"),
    cl::value_desc("directory"), cl::cat(CppVerifyCategory));

static cl::opt<bool> LeanCertify(
    "lean-certify",
    cl::desc("Kernel-check every proof in --lean-project without admissions"),
    cl::init(false), cl::cat(CppVerifyCategory));

static cl::opt<unsigned>
    BMCUnroll("unroll", cl::desc("Loop unroll bound for --backend=bmc"),
              cl::init(10), cl::cat(CppVerifyCategory));

static cl::opt<unsigned> SolverTimeout(
    "timeout",
    cl::desc(
        "Per-query Z3 timeout in milliseconds (0 = no limit). A query that "
        "exceeds it is reported as unresolved instead of hanging"),
    cl::init(verify::DefaultSolverTimeoutMs), cl::cat(CppVerifyCategory));

static cl::opt<unsigned> SolverResourceLimit(
    "solver-rlimit",
    cl::desc("Per-query deterministic Z3 resource limit (0 = no limit)"),
    cl::init(0), cl::cat(CppVerifyCategory));

static cl::opt<unsigned>
    Jobs("jobs",
         cl::desc("Isolated Z3 solver jobs (0 = available physical cores)"),
         cl::init(1), cl::cat(CppVerifyCategory));

static cl::opt<uint64_t>
    MaxQueryNodes("max-query-nodes",
                  cl::desc("Maximum canonical expression nodes per Z3-backed "
                           "module (0 = no limit)"),
                  cl::init(0), cl::cat(CppVerifyCategory));

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
    cl::desc("Enable valid(p, n)-based buffer bounds checks in addition to "
             "always-on expression definedness checks"),
    cl::init(false), cl::cat(CppVerifyCategory));

static cl::opt<std::string> ObligationOut(
    "obligation-out",
    cl::desc("Write versioned backend-neutral obligation modules to this file"),
    cl::value_desc("file"), cl::cat(CppVerifyCategory));

static cl::opt<std::string> ObligationIn(
    "obligation-in",
    cl::desc("Validate and replay a backend-neutral obligation archive"),
    cl::value_desc("file"), cl::cat(CppVerifyCategory));

static cl::opt<verify::DiagnosticFormat> DiagnosticsFormat(
    "diagnostics-format", cl::desc("Verification diagnostics format"),
    cl::values(clEnumValN(verify::DiagnosticFormat::Text, "text",
                          "Human-readable text (default)"),
               clEnumValN(verify::DiagnosticFormat::Json, "json",
                          "Versioned JSON Lines")),
    cl::init(verify::DiagnosticFormat::Text), cl::cat(CppVerifyCategory));

namespace {

static int gVerifyFailures = 0;
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
  Options.SolverResourceLimit = SolverResourceLimit;
  Options.Jobs = Jobs;
  Options.MaxQueryNodes = MaxQueryNodes;
  Options.ProofCachePath = ProofCache;
  Options.ProofCacheMaxBytes = proofCacheMaxBytes();
  Options.ProofCacheMaxEntries = ProofCacheMaxEntries;
  return Options;
}

class VerifyConsumer : public ASTConsumer {
public:
  void HandleTranslationUnit(ASTContext &Ctx) override {
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
      else
        VOpts.Backend = verify::BackendKind::Z3;
      VOpts.LeanOutPath = LeanOut.getValue();
      VOpts.LeanProjectPath = LeanProject.getValue();
      VOpts.LeanFallbackProjectPath = LeanFallback.getValue();
      VOpts.LeanCertify = LeanCertify.getValue();
      VOpts.BMCUnroll = BMCUnroll.getValue();
      VOpts.SolverTimeoutMs = SolverTimeout.getValue();
      VOpts.SolverResourceLimit = SolverResourceLimit.getValue();
      VOpts.Jobs = Jobs.getValue();
      VOpts.MaxQueryNodes = MaxQueryNodes.getValue();
      VOpts.ProofCachePath = ProofCache.getValue();
      VOpts.ProofCacheMaxBytes = proofCacheMaxBytes();
      VOpts.ProofCacheMaxEntries = ProofCacheMaxEntries.getValue();
      VOpts.CheckUB = CheckUB.getValue();
      VOpts.Diagnostics = DiagnosticsFormat.getValue();
      VOpts.ObligationOut = gObligationOut;
      if (!verify::verifyTranslationUnit(Ctx, llvm::outs(), VOpts))
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

static llvm::StringRef replayStatusCode(verify::VerifyStatus Status) {
  switch (Status) {
  case verify::VerifyStatus::Lowered:
    return "lowered";
  case verify::VerifyStatus::Verified:
    return "verified";
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
  }
  return "unresolved";
}

static std::string jsonText(llvm::StringRef Text) {
  return llvm::json::isUTF8(Text) ? Text.str() : llvm::json::fixUTF8(Text);
}

static llvm::json::Object
replaySourceJSON(const verify::ObligationSource &Source) {
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

static void printReplayJSON(const verify::ObligationModule &Module,
                            const verify::VerifyResult &Result,
                            llvm::StringRef SemanticHash) {
  llvm::json::Object Record;
  Record["schema"] = "cppverify.diagnostic/1";
  Record["status"] = replayStatusCode(Result.Status);
  Record["severity"] = Result.Status == verify::VerifyStatus::BoundedSafe
                           ? "warning"
                       : Result.Status == verify::VerifyStatus::Failed ||
                               Result.Status == verify::VerifyStatus::Unresolved
                           ? "error"
                           : "note";
  Record["function"] = jsonText(Module.FunctionName);
  Record["message"] = jsonText(Result.Message);
  Record["semantic_hash"] = ("sha256:" + SemanticHash).str();
  if (!Result.BackendName.empty())
    Record["backend"] = Result.BackendName;
  if (Result.Reason != verify::VerifyReason::None)
    Record["reason"] = verify::verifyReasonCode(Result.Reason);
  if (Result.Bound)
    Record["bound"] = static_cast<int64_t>(*Result.Bound);
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
    Record["source"] = replaySourceJSON(Result.Source);
  if (!Result.ObligationId.empty()) {
    llvm::json::Object Obligation;
    Obligation["id"] = jsonText(Result.ObligationId);
    if (Result.ObligationType) {
      const char *Kind =
          *Result.ObligationType == verify::ObligationKind::Postcondition
              ? "postcondition"
          : *Result.ObligationType == verify::ObligationKind::Unwinding
              ? "unwinding"
              : "assertion";
      Obligation["kind"] = Kind;
    }
    if (Result.Source.isValid())
      Obligation["source"] = replaySourceJSON(Result.Source);
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
        Entry["source"] = replaySourceJSON(Value.Source);
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
      Entry["active"] = Event.Active ? llvm::json::Value(*Event.Active)
                                     : llvm::json::Value(nullptr);
      if (Event.Source.isValid())
        Entry["source"] = replaySourceJSON(Event.Source);
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
  llvm::outs() << llvm::formatv("{0}\n", llvm::json::Value(std::move(Record)));
}

static int replayObligationArchive() {
  if (!ObligationOut.empty()) {
    llvm::errs() << "error: --obligation-in and --obligation-out are mutually "
                    "exclusive\n";
    return 1;
  }
  if (!LeanProject.empty() || !LeanFallback.empty() || LeanCertify) {
    llvm::errs() << "error: archive replay supports Lean scratch-pad export "
                    "with --lean-out, not Lean project generation or "
                    "certification\n";
    return 1;
  }
  if (BackendOpt == "lean" && (Jobs != 1 || !ProofCache.empty())) {
    llvm::errs()
        << "error: --jobs and --proof-cache apply only to Z3-backed replay\n";
    return 1;
  }
  if (LowerOnly && !ProofCache.empty()) {
    llvm::errs()
        << "error: --proof-cache cannot be combined with --lower-only\n";
    return 1;
  }

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
    if (BackendOpt == "lean" && Module.BMCTransform) {
      llvm::errs() << "error: Lean scratch export cannot replay a "
                      "BMC-transformed obligation archive\n";
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
  if (BackendOpt == "lean") {
    if (LeanOut.empty()) {
      llvm::errs()
          << "error: --backend=lean archive replay requires --lean-out\n";
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

  verify::BackendKind Kind = BackendOpt == "lean" ? verify::BackendKind::Lean
                                                  : verify::BackendKind::Z3;
  std::unique_ptr<verify::VerifyBackend> Backend = verify::createVerifyBackend(
      Kind, LeanStream, BMCUnroll, backendExecutionOptions());
  const unsigned DumpLayers = DumpIR.getNumOccurrences() > 0
                                  ? verify::parseDumpIRLayers(DumpIR.getValue())
                                  : 0;
  bool AllOk = true;
  for (const verify::ObligationModule &Module : Modules) {
    if (DumpLayers & verify::LayerVC)
      verify::dumpVC(Module, llvm::outs());

    verify::VerifyResult Result;
    if (LowerOnly) {
      Result = verify::lowerObligationModule(
          Module, DumpLayers & verify::LayerZ3 ? &llvm::outs() : nullptr,
          backendExecutionOptions());
      if (Result.BackendName.empty())
        Result.BackendName = "z3";
    } else {
      if (Module.BMCTransform) {
        std::unique_ptr<verify::VerifyBackend> BMCBackend =
            verify::createVerifyBackend(verify::BackendKind::BMC, nullptr,
                                        Module.BMCTransform->UnrollBound,
                                        backendExecutionOptions());
        Result = BMCBackend->verify(Module);
      } else {
        Result = Backend->verify(Module);
      }
    }

    const std::string Hash = verify::obligationSemanticHash(Module);
    if (DiagnosticsFormat == verify::DiagnosticFormat::Json) {
      printReplayJSON(Module, Result, Hash);
      if (Result.Status != verify::VerifyStatus::Lowered &&
          Result.Status != verify::VerifyStatus::Verified &&
          Result.Status != verify::VerifyStatus::Exported)
        AllOk = false;
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
      llvm::outs() << "Verified: " << Module.FunctionName << Suffix << "\n";
      break;
    case verify::VerifyStatus::Exported:
      llvm::outs() << "Exported: lean obligation: " << Module.FunctionName
                   << Suffix << "\n";
      break;
    case verify::VerifyStatus::Failed:
      AllOk = false;
      printResultSource();
      llvm::outs() << "error: verification failed: " << Module.FunctionName;
      if (!Result.ObligationId.empty())
        llvm::outs() << " [" << Result.ObligationId << "]";
      if (!Result.Message.empty())
        llvm::outs() << " (counterexample: " << Result.Message << ")";
      llvm::outs() << Suffix << "\n";
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
      AllOk = false;
      llvm::outs() << "Unresolved: " << Module.FunctionName
                   << " (archive backend returned an invalid replay status)"
                   << Suffix << "\n";
      break;
    }
  }
  if (LeanFile) {
    LeanFile->flush();
    if (LeanFile->has_error()) {
      llvm::errs() << "error: cannot write Lean output\n";
      return 1;
    }
  }
  return AllOk ? 0 : 1;
}

} // namespace

int main(int argc, const char **argv) {
  llvm::InitLLVM X(argc, argv);

  static const char ReplayPlaceholder[] = "cppverify-obligation-replay.cpp";
  bool HasObligationInput = false;
  for (int I = 1; I < argc; ++I) {
    llvm::StringRef Arg(argv[I]);
    if (Arg == "--obligation-in" || Arg.starts_with("--obligation-in=")) {
      HasObligationInput = true;
      break;
    }
  }
  std::vector<const char *> AdjustedArgv;
  if (HasObligationInput) {
    AdjustedArgv.assign(argv, argv + argc);
    AdjustedArgv.push_back(ReplayPlaceholder);
    argv = AdjustedArgv.data();
    argc = static_cast<int>(AdjustedArgv.size());
  }

  auto ExpectedParser =
      CommonOptionsParser::create(argc, argv, CppVerifyCategory);
  if (!ExpectedParser) {
    llvm::errs() << toString(ExpectedParser.takeError()) << "\n";
    return 1;
  }
  CommonOptionsParser &OptionsParser = ExpectedParser.get();
  StringRef Backend = BackendOpt.getValue();
  if (Backend != "z3" && Backend != "lean" && Backend != "bmc") {
    llvm::errs() << "error: unknown verification backend '" << Backend
                 << "'; expected z3, lean, or bmc\n";
    return 1;
  }
  if (!ObligationIn.empty()) {
    const std::vector<std::string> &Sources = OptionsParser.getSourcePathList();
    if (Sources.size() != 1 || Sources.front() != ReplayPlaceholder) {
      llvm::errs() << "error: --obligation-in cannot be combined with C++ "
                      "source files\n";
      return 1;
    }
    return replayObligationArchive();
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

  ClangTool Tool(OptionsParser.getCompilations(),
                 OptionsParser.getSourcePathList());
  Tool.appendArgumentsAdjuster(OptionsParser.getArgumentsAdjuster());
  Tool.appendArgumentsAdjuster(getInsertArgumentAdjuster(
      {"-fverify-contracts", "-std=c++17"}, ArgumentInsertPosition::BEGIN));
#if defined(__APPLE__)
  if (const char *SDK = std::getenv("SDKROOT"); SDK && SDK[0])
    Tool.appendArgumentsAdjuster(getInsertArgumentAdjuster(
        {"-isysroot", SDK}, ArgumentInsertPosition::BEGIN));
#endif

  int RC = Tool.run(newFrontendActionFactory<VerifyAction>().get());
  if (RC != 0)
    return RC;
  if (ObligationFile) {
    ObligationFile->flush();
    if (ObligationFile->has_error()) {
      llvm::errs() << "error: cannot write obligation archive\n";
      return 1;
    }
  }
  return gVerifyFailures > 0 ? 1 : 0;
}