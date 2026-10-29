//===--- CppVerifyIntegration.h - verification in a compilation -----------===//
#ifndef LLVM_CLANG_VERIFY_DRIVER_CPPVERIFY_INTEGRATION_H
#define LLVM_CLANG_VERIFY_DRIVER_CPPVERIFY_INTEGRATION_H

#include "Verifier.h"

namespace clang {
class ASTContext;
class CompilerInstance;
class FrontendOptions;

namespace verify {

/// The verifier's options for a compilation with \p Options' -fverify-*
/// options, as cpp-verify's options of the same names set them: a query
/// timeout also scales the collection and function timeouts. A file without
/// a function to verify says nothing.
VerifyOptions compilationOptions(const FrontendOptions &Options);

/// Returns true if CppVerify SMT should run for this compilation.
bool shouldRunCppVerify(const CompilerInstance &CI);

/// Verify \p Ctx with the -fverify-* options of \p CI and report the results
/// through its diagnostics: failures as errors with notes, warnings in
/// -Wcppverify, and proofs as remarks (-Rcppverify). It must run before IR
/// generation, not beside it: CodeGen fills caches of the ASTContext and the
/// SourceManager that the verifier reads. With -fverify-contracts-out,
/// contracts declared without a definition are assumed and recorded there
/// with those verified, for cpp-verify --check-contracts.
bool runCppVerify(CompilerInstance &CI, ASTContext &Ctx);

} // namespace verify
} // namespace clang

#endif