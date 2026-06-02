//===--- Z3Encode.h - VExpr to Z3 ---------------------------------*- C++ -*-===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_Z3ENCODE_H
#define LLVM_CLANG_VERIFY_BACKEND_Z3ENCODE_H

#include "../IR/VExpr.h"
#include "../Transform/Passivize.h"
#include <map>
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
  z3::sort heapSort();
  z3::expr heapVar(const std::string &Name);
  z3::expr encodeExpr(const VExpr *E, const std::string &CurHeap);
  z3::expr encodeHeapStore(const VHeapStoreExpr *H);
  z3::expr expandQuantifier(const VQuantifiedExpr *Q, bool IsForall);
  std::string ResultVarName;

public:
  Z3Encoder();
  Z3CheckResult verifyPassive(const PassiveProgram &P);
  Z3CheckResult checkVC(const VExpr *VC);
  void dumpVC(const VExpr *VC, llvm::raw_ostream &OS);
};

} // namespace verify
} // namespace clang

#endif