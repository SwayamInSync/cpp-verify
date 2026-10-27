//===--- DiagnosticPart.h -------------------------------------------------===//
#ifndef LLVM_CLANG_VERIFY_DRIVER_DIAGNOSTICPART_H
#define LLVM_CLANG_VERIFY_DRIVER_DIAGNOSTICPART_H

#include "clang/Basic/Diagnostic.h"
#include "clang/Basic/SourceLocation.h"
#include <string>

namespace clang {
namespace verify {

/// One Clang diagnostic of a verification result: its line, or a note.
struct VerifyDiagnosticPart {
  DiagnosticsEngine::Level Level = DiagnosticsEngine::Note;
  SourceLocation Loc;
  SourceRange Range;
  std::string Message;
};

} // namespace verify
} // namespace clang

#endif
