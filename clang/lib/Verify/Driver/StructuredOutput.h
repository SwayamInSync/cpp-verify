//===--- StructuredOutput.h - JSON, SARIF, and GitHub output ----*- C++ -*-===//
#ifndef LLVM_CLANG_VERIFY_DRIVER_STRUCTUREDOUTPUT_H
#define LLVM_CLANG_VERIFY_DRIVER_STRUCTUREDOUTPUT_H

#include "../Backend/Obligation.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/JSON.h"
#include <string>
#include <vector>

namespace clang {
namespace verify {

inline constexpr const char DiagnosticSchema[] = "cppverify.diagnostic/2";
inline constexpr const char SummarySchema[] = "cppverify.summary/1";

/// Text as JSON takes it: invalid UTF-8 replaced.
std::string jsonText(llvm::StringRef Text);

/// The source a term spans, from its first column to the one after its last.
llvm::json::Object sourceJSON(const ObligationSource &Source);

/// A GitHub workflow command that annotates Source (an error, a warning, or a
/// notice) with Title and Message.
std::string githubCommand(llvm::StringRef Level, const ObligationSource &Source,
                          llvm::StringRef Title, llvm::StringRef Message);

/// How the run that produced the records went.
struct SarifInvocation {
  std::string Version;
  std::vector<std::string> Arguments;
  int ExitCode = 0;
};

/// A SARIF 2.1.0 log of the records of a run: cppverify.diagnostic/2 records
/// become results, and the summary and time records the run's properties.
llvm::json::Value sarifLog(llvm::ArrayRef<llvm::json::Value> Records,
                           const SarifInvocation &Invocation);

} // namespace verify
} // namespace clang

#endif
