//===--- Z3Encode.h - VCMachine to Z3 -----------------------------------===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_Z3ENCODE_H
#define LLVM_CLANG_VERIFY_BACKEND_Z3ENCODE_H

#include "SpecAxioms.h"
#include "VCMachine.h"
#include "VerifyBackend.h"
#include "../IR/VType.h"
#include <map>
#include <set>
#include <string>
#include <z3++.h>

namespace clang {
namespace verify {

class Z3Encoder {
  z3::context Ctx;
  z3::solver Solver;
  std::map<std::string, z3::expr> Vars;
  FunctionMap SpecFunctions;
  std::map<std::string, z3::func_decl> SpecFuncDecls;
  VIntMode CallerIntMode = VIntMode::Machine;

  z3::sort intSort();
  z3::sort bvSort();
  z3::sort boolSort();
  z3::sort heapSort();
  z3::sort valueSort(const VType &Ty, VIntMode Mode);
  z3::expr heapVar(const std::string &Name);
  z3::expr coerceTo(z3::expr E, VIntMode Target);
  z3::func_decl specFuncDecl(const VFunction *Spec);
  z3::expr encodeVCNode(const VCExpr *E,
                        const std::map<const VCExpr *, z3::expr> &Done);
  z3::expr encodeVC(const VCExpr *E);
  z3::expr encodeVExprForAxiom(const VExpr *E, const VType &RetTy);

public:
  Z3Encoder();
  VerifyResult verifyMachine(const VCMachine &M);
  void emitSpecDefiningAxiom(const std::string &Name, const SpecAxiomContext &Ctx);
  void dumpVC(const VCExpr *E, llvm::raw_ostream &OS);
};

class Z3VerifyBackend : public VerifyBackend {
  Z3Encoder Enc;

public:
  llvm::StringRef getName() const override { return "z3"; }
  VerifyResult verifyPassive(const PassiveProgram &P) override;
};

} // namespace verify
} // namespace clang

#endif