//===--- CppVerifyIntegration.h - parallel SMT + codegen hook -------------===//
#ifndef LLVM_CLANG_VERIFY_DRIVER_CPPVERIFY_INTEGRATION_H
#define LLVM_CLANG_VERIFY_DRIVER_CPPVERIFY_INTEGRATION_H

#include <future>
#include <string>
#include <utility>

namespace clang {
class ASTContext;
class CompilerInstance;

namespace verify {

using CppVerifyAsyncResult = std::pair<bool, std::string>;

/// Returns true if CppVerify SMT should run for this compilation.
bool shouldRunCppVerify(const CompilerInstance &CI);

/// Start SMT verification on \p Ctx in a background thread. The AST must not be
/// mutated while the future is pending (safe during codegen IR generation).
/// With \p ContractsOut, contracts declared without a definition are assumed
/// and recorded there with those verified, for cpp-verify --check-contracts.
std::future<CppVerifyAsyncResult>
startCppVerifyAsync(ASTContext &Ctx, std::string ContractsOut = "");

/// Join \p Future, print verifier output, and report diagnostics on failure.
bool finishCppVerify(CompilerInstance &CI, std::future<CppVerifyAsyncResult> Future);

} // namespace verify
} // namespace clang

#endif