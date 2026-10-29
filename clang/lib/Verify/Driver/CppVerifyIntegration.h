//===--- CppVerifyIntegration.h - parallel SMT + codegen hook -------------===//
#ifndef LLVM_CLANG_VERIFY_DRIVER_CPPVERIFY_INTEGRATION_H
#define LLVM_CLANG_VERIFY_DRIVER_CPPVERIFY_INTEGRATION_H

#include "DiagnosticPart.h"
#include "Verifier.h"
#include <future>
#include <string>
#include <vector>

namespace clang {
class ASTContext;
class CompilerInstance;
class FrontendOptions;

namespace verify {

/// Whether verification succeeded, and its results as Clang diagnostics.
struct CppVerifyAsyncResult {
  bool Ok = false;
  std::vector<VerifyDiagnosticPart> Parts;
};

/// The verifier's options for a compilation with \p Options' -fverify-*
/// options, as cpp-verify's options of the same names set them: a query
/// timeout also scales the collection and function timeouts. A file without
/// a function to verify says nothing.
VerifyOptions compilationOptions(const FrontendOptions &Options);

/// Returns true if CppVerify SMT should run for this compilation.
bool shouldRunCppVerify(const CompilerInstance &CI);

/// Start SMT verification on \p Ctx in a background thread, with the
/// -fverify-* options of \p Options. The AST must not be mutated while the
/// future is pending (safe during codegen IR generation). With
/// -fverify-contracts-out, contracts declared without a definition are
/// assumed and recorded there with those verified, for cpp-verify
/// --check-contracts.
std::future<CppVerifyAsyncResult>
startCppVerifyAsync(ASTContext &Ctx, const FrontendOptions &Options);

/// Join \p Future and report its results through the compiler's diagnostics:
/// failures as errors with notes, warnings in -Wcppverify, and proofs as
/// remarks (-Rcppverify).
bool finishCppVerify(CompilerInstance &CI, std::future<CppVerifyAsyncResult> Future);

} // namespace verify
} // namespace clang

#endif