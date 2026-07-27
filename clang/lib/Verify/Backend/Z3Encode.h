//===--- Z3Encode.h - Obligation IR to Z3 -----------------------*- C++ -*-===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_Z3ENCODE_H
#define LLVM_CLANG_VERIFY_BACKEND_Z3ENCODE_H

#include "../IR/VType.h"
#include "Obligation.h"
#include "SpecAxioms.h"
#include "VerifyBackend.h"
#include <map>
#include <optional>
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
  unsigned TimeoutMs = 0;
  bool EncodingFailed = false;
  std::string EncodingError;

  z3::sort intSort();
  z3::sort bvSort(unsigned BitWidth);
  z3::sort boolSort();
  z3::sort heapSort();
  z3::sort valueSort(const VType &Ty, VIntMode Mode);
  z3::expr heapVar(const std::string &Name);
  z3::expr coerceTo(z3::expr E, VIntMode Target, unsigned BitWidth,
                    bool IsSigned = true);
  z3::expr asBool(z3::expr E);
  z3::expr fallbackValue(const VCExpr *E);
  z3::expr arithOp(const VCExpr *E, z3::expr L, z3::expr R);
  void markEncodingFailure(std::string Message);
  z3::func_decl specFuncDecl(const VFunction *Spec);
  z3::expr encodeVCNode(const VCExpr *E,
                        const std::map<const VCExpr *, z3::expr> &Done);
  z3::expr encodeVC(const VCExpr *E);
  std::optional<z3::expr> encodeModule(const ObligationModule &Module,
                                       const LogicExpr *Query,
                                       VerifyResult &Result);
  z3::expr encodeVExprForAxiom(const VExpr *E, const VType &RetTy,
                               VIntMode SpecMode);

public:
  Z3Encoder();
  void setTimeoutMs(unsigned Ms) { TimeoutMs = Ms; }
  VerifyResult verifyModule(const ObligationModule &Module,
                            const LogicExpr *Query = nullptr);
  VerifyResult lowerModule(const ObligationModule &Module,
                           llvm::raw_ostream *OS = nullptr);
  void emitSpecCallAxiom(const VCExpr *Call, const SpecAxiomContext &Ctx);
};

class Z3VerifyBackend : public VerifyBackend {
  Z3Encoder Enc;
  unsigned TimeoutMs;

public:
  explicit Z3VerifyBackend(unsigned TimeoutMs = 0) : TimeoutMs(TimeoutMs) {
    Enc.setTimeoutMs(TimeoutMs);
  }
  llvm::StringRef getName() const override { return "z3"; }
  BackendCapabilities getCapabilities() const override {
    return {allLogicFeatures(), true};
  }

protected:
  VerifyResult verifyModule(const ObligationModule &Module) override;
};

} // namespace verify
} // namespace clang

#endif