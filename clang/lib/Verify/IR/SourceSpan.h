//===--- SourceSpan.h - A place in the source and its extent ----*- C++ -*-===//
#ifndef LLVM_CLANG_VERIFY_IR_SOURCESPAN_H
#define LLVM_CLANG_VERIFY_IR_SOURCESPAN_H

#include "clang/Basic/SourceLocation.h"

namespace clang {
namespace verify {

/// Where an expression is: the anchor a caret points at (an operator, a
/// callee's name), and where the expression begins and ends.
struct SourceSpan {
  SourceLocation Loc;
  SourceLocation BeginLoc;
  SourceLocation EndLoc;

  bool isValid() const { return Loc.isValid(); }
};

} // namespace verify
} // namespace clang

#endif
