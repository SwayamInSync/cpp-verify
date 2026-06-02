//===--- WPCalc.h - Weakest precondition calculus -----------------*- C++ -*-===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_WPCALC_H
#define LLVM_CLANG_VERIFY_BACKEND_WPCALC_H

#include "../Transform/Passivize.h"
#include <memory>

namespace clang {
namespace verify {

class WPCalculator {
public:
  std::unique_ptr<VExpr> computeVC(const PassiveProgram &P);
};

} // namespace verify
} // namespace clang

#endif