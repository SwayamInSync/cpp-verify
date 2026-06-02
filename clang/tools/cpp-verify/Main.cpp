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

namespace {

class VerifyConsumer : public ASTConsumer {
public:
  void HandleTranslationUnit(ASTContext &Ctx) override {
    if (!Ctx.getDiagnostics().getClient()->getNumErrors()) {
      verify::VerifyOptions VOpts;
      if (DumpIR.getNumOccurrences() > 0)
        VOpts.DumpIRLayers = verify::parseDumpIRLayers(DumpIR.getValue());
      verify::verifyTranslationUnit(Ctx, llvm::outs(), VOpts);
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

  return Tool.run(newFrontendActionFactory<VerifyAction>().get());
}