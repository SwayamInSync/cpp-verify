//===--- LoopUnroll.h - Bounded loop unrolling for BMC ------------------===//
#ifndef LLVM_CLANG_VERIFY_TRANSFORM_LOOPUNROLL_H
#define LLVM_CLANG_VERIFY_TRANSFORM_LOOPUNROLL_H

#include "../IR/VStmt.h"

namespace clang {
namespace verify {

class LoopUnroller {
public:
  static VFunction unroll(const VFunction &Fn, unsigned K);
};

} // namespace verify
} // namespace clang

#endif