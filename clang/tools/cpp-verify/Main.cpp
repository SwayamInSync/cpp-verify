//===--- Main.cpp - cpp-verify standalone tool ----------------------------===//
#include "Verifier.h"
#include "DumpIR.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ASTContext.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/InitLLVM.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>

using namespace clang;
using namespace clang::tooling;
using namespace llvm;

static cl::OptionCategory CppVerifyCategory("cpp-verify options");
static cl::extrahelp CommonHelp(CommonOptionsParser::HelpMessage);
static cl::opt<std::string> DumpIR(
    "dump-ir",
    cl::desc("Dump verification IR (layers: 1=vcr 2=passive 3=vc 4=z3; "
             "comma-separated, default all)"),
    cl::value_desc("layers"),
    cl::ValueOptional,
    cl::cat(CppVerifyCategory));

static cl::opt<std::string> BackendOpt(
    "backend",
    cl::desc("Verification backend: z3 (default), lean, bmc"),
    cl::value_desc("name"),
    cl::init("z3"),
    cl::cat(CppVerifyCategory));

static cl::opt<std::string> LeanOut(
    "lean-out",
    cl::desc("Output path for --backend=lean scratch-pad export"),
    cl::value_desc("file"),
    cl::cat(CppVerifyCategory));

static cl::opt<unsigned> BMCUnroll(
    "unroll",
    cl::desc("Loop unroll bound for --backend=bmc"),
    cl::init(10),
    cl::cat(CppVerifyCategory));

static cl::opt<unsigned> SolverTimeout(
    "timeout",
    cl::desc("Per-query Z3 timeout in milliseconds (0 = no limit). A query that "
             "exceeds it is reported as unknown instead of hanging"),
    cl::init(10000),
    cl::cat(CppVerifyCategory));

namespace {

static int gVerifyFailures = 0;

class VerifyConsumer : public ASTConsumer {
public:
  void HandleTranslationUnit(ASTContext &Ctx) override {
    if (!Ctx.getDiagnostics().getClient()->getNumErrors()) {
      verify::VerifyOptions VOpts;
      if (DumpIR.getNumOccurrences() > 0)
        VOpts.DumpIRLayers = verify::parseDumpIRLayers(DumpIR.getValue());
      llvm::StringRef B = BackendOpt.getValue();
      if (B == "lean")
        VOpts.Backend = verify::BackendKind::Lean;
      else if (B == "bmc")
        VOpts.Backend = verify::BackendKind::BMC;
      else
        VOpts.Backend = verify::BackendKind::Z3;
      VOpts.LeanOutPath = LeanOut.getValue();
      VOpts.BMCUnroll = BMCUnroll.getValue();
      VOpts.SolverTimeoutMs = SolverTimeout.getValue();
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

} // namespace

int main(int argc, const char **argv) {
  llvm::InitLLVM X(argc, argv);

  auto ExpectedParser =
      CommonOptionsParser::create(argc, argv, CppVerifyCategory);
  if (!ExpectedParser) {
    llvm::errs() << toString(ExpectedParser.takeError()) << "\n";
    return 1;
  }
  CommonOptionsParser &OptionsParser = ExpectedParser.get();

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
  return gVerifyFailures > 0 ? 1 : 0;
}