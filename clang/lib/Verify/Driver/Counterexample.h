//===--- Counterexample.h -------------------------------------------------===//
#ifndef LLVM_CLANG_VERIFY_DRIVER_COUNTEREXAMPLE_H
#define LLVM_CLANG_VERIFY_DRIVER_COUNTEREXAMPLE_H

#include "../Backend/VerifyBackend.h"
#include <string>

namespace clang {
namespace verify {

/// A counterexample's values by source name, in the order the source
/// declares them, each variable's versions in program order:
/// "a = 100, i = 0 -> 1, result = 151". Empty when it has none.
std::string counterexampleText(const VerifyResult &Result);

/// One step of a counterexample's path, as the static analyzer words its
/// path notes: "takes the false branch", "returns 151".
std::string traceStepText(const VerifyTraceEvent &Event);

/// How many steps of a path are shown: the first and last half of them, as
/// -ftemplate-backtrace-limit shows instantiation contexts.
inline constexpr size_t TraceStepLimit = 10;

} // namespace verify
} // namespace clang

#endif
