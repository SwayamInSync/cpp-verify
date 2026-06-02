//===--- Z3Encode.h - VExpr to Z3 ---------------------------------*- C++ -*-===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_Z3ENCODE_H
#define LLVM_CLANG_VERIFY_BACKEND_Z3ENCODE_H

#include "../IR/VExpr.h"
#include <map>
#include <memory>
#include <string>
#include <z3++.h>

namespace clang {
namespace verify {

struct Z3CheckResult {
  enum Status { Verified, Failed, Unknown };
  Status S = Unknown;
  std::string Counterexample;
};

class Z3Encoder {
  z3::context Ctx;
  z3::solver Solver;
  std::map<std::string, z3::expr> Vars;

  z3::sort intSort();
  z3::sort boolSort();
  z3::expr encodeExpr(const VExpr *E);

public:
  Z3Encoder();
  Z3CheckResult checkVC(const VExpr *VC);
  void dumpVC(const VExpr *VC, llvm::raw_ostream &OS);
};

} // namespace verify
} // namespace clang

#endif