//===--- CppVerifyIntegration.cpp -----------------------------------------===//
#include "CppVerifyIntegration.h"
#include "Verifier.h"
#include "clang/Basic/DiagnosticFrontend.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendOptions.h"
#include <limits>
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

VerifyOptions verify::compilationOptions(const FrontendOptions &Options) {
  VerifyOptions Opts;
  switch (Options.VerifyBackend) {
  case FrontendOptions::CppVerifyBackend::Z3:
    Opts.Backend = BackendKind::Z3;
    break;
  case FrontendOptions::CppVerifyBackend::CVC5:
    Opts.Backend = BackendKind::CVC5;
    break;
  case FrontendOptions::CppVerifyBackend::Portfolio:
    Opts.Backend = BackendKind::Portfolio;
    break;
  case FrontendOptions::CppVerifyBackend::Race:
    Opts.Backend = BackendKind::Race;
    break;
  case FrontendOptions::CppVerifyBackend::BMC:
    Opts.Backend = BackendKind::BMC;
    break;
  }
  const unsigned Timeout = Options.VerifyTimeoutMs;
  const unsigned Max = std::numeric_limits<unsigned>::max();
  Opts.SolverTimeoutMs = Timeout;
  Opts.CollectionTimeoutMs = Timeout > Max / 2 ? 0 : 2 * Timeout;
  Opts.FunctionTimeoutMs = Timeout > Max / 10 ? 0 : 10 * Timeout;
  Opts.Jobs = std::max(1u, Options.VerifyJobs);
  Opts.ProofCachePath = Options.VerifyCache;
  Opts.ReportPath = Options.VerifyReport;
  Opts.ContractsOut = Options.VerifyContractsOut;
  Opts.QuietWithoutFunctions = true;
  return Opts;
}

std::future<CppVerifyAsyncResult>
verify::startCppVerifyAsync(ASTContext &Ctx, const FrontendOptions &Options) {
  return std::async(std::launch::async,
                    [&Ctx, Opts = compilationOptions(Options)]() mutable {
                      CppVerifyAsyncResult Result;
                      Opts.Parts = &Result.Parts;
                      Result.Ok =
                          verifyTranslationUnit(Ctx, llvm::nulls(), Opts);
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