//===--- CppVerifyIntegration.cpp -----------------------------------------===//
#include "CppVerifyIntegration.h"
#include "Verifier.h"
#include "clang/Basic/DiagnosticFrontend.h"
#include "clang/Frontend/CompilerInstance.h"
#include "llvm/Support/raw_ostream.h"
#include <thread>

using namespace clang;
using namespace verify;

bool verify::shouldRunCppVerify(const CompilerInstance &CI) {
  if (!CI.getLangOpts().VerifyContracts)
    return false;
  if (!CI.getFrontendOpts().RunCppVerify)
    return false;
  if (CI.getDiagnostics().hasUnrecoverableErrorOccurred())
    return false;
  return true;
}

std::future<CppVerifyAsyncResult>
verify::startCppVerifyAsync(ASTContext &Ctx, std::string ContractsOut) {
  return std::async(std::launch::async, [&Ctx, ContractsOut]() {
    CppVerifyAsyncResult Result;
    VerifyOptions Opts;
    Opts.ContractsOut = ContractsOut;
    Opts.Parts = &Result.Parts;
    Result.Ok = verifyTranslationUnit(Ctx, llvm::nulls(), Opts);
    return Result;
  });
}

bool verify::finishCppVerify(CompilerInstance &CI,
                             std::future<CppVerifyAsyncResult> Future) {
  CppVerifyAsyncResult R = Future.get();
  DiagnosticsEngine &Diags = CI.getDiagnostics();
  bool Reported = false;
  for (const VerifyDiagnosticPart &Part : R.Parts) {
    unsigned ID = diag::note_cppverify_result;
    switch (Part.Level) {
    case DiagnosticsEngine::Error:
    case DiagnosticsEngine::Fatal:
      ID = diag::err_cppverify_result;
      Reported = true;
      break;
    case DiagnosticsEngine::Warning:
      ID = diag::warn_cppverify_result;
      break;
    case DiagnosticsEngine::Remark:
      ID = diag::remark_cppverify_result;
      break;
    case DiagnosticsEngine::Note:
    case DiagnosticsEngine::Ignored:
      break;
    }
    DiagnosticBuilder Builder = Diags.Report(Part.Loc, ID);
    Builder << Part.Message;
    if (Part.Range.isValid())
      Builder << CharSourceRange::getTokenRange(Part.Range);
  }
  // A failure without a result of its own still fails the compilation.
  if (!R.Ok && !Reported)
    Diags.Report(diag::err_fe_cppverify_failed) << "verification failed";
  return R.Ok;
}