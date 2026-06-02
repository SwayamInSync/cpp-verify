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
verify::startCppVerifyAsync(ASTContext &Ctx) {
  return std::async(std::launch::async, [&Ctx]() {
    std::string Buffer;
    llvm::raw_string_ostream OS(Buffer);
    bool Ok = verifyTranslationUnit(Ctx, OS, VerifyOptions{});
    OS.flush();
    return CppVerifyAsyncResult{Ok, std::move(Buffer)};
  });
}

bool verify::finishCppVerify(CompilerInstance &CI,
                             std::future<CppVerifyAsyncResult> Future) {
  CppVerifyAsyncResult R = Future.get();
  if (!R.second.empty())
    llvm::errs() << R.second;
  if (!R.first) {
    CI.getDiagnostics().Report(diag::err_fe_cppverify_failed)
        << "verification failed";
    return false;
  }
  return true;
}