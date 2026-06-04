//===--- Z3Encode.h - VCMachine to Z3 -----------------------------------===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_Z3ENCODE_H
#define LLVM_CLANG_VERIFY_BACKEND_Z3ENCODE_H

#include "SpecAxioms.h"
#include "VCMachine.h"
#include "VerifyBackend.h"
#include "../IR/VType.h"
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
  /// Per-query solver timeout in milliseconds; 0 disables it. Prevents
  /// non-terminating queries from hanging the tool (they return Unknown).
  unsigned TimeoutMs = 0;

  /// Reveal fuel per spec function, used to pick the fuel depth of recursive
  /// spec calls at goal sites. Populated from the VCMachine before encoding.
  std::map<std::string, unsigned> SpecFuelMap;

  /// Fuel encoding for recursive spec functions (Verus/Dafny style). A
  /// recursive spec `f` is declared with an extra leading `Fuel` argument; its
  /// defining axioms (unfold + synonym) are triggered on `f(Succ(g), args)`, so
  /// unfolding is bounded by the syntactic Succ-depth of the fuel term and the
  /// recursive leaves remain the same function rather than fresh constants.
  std::optional<z3::sort> FuelSortOpt;
  std::optional<z3::func_decl> FuelSuccOpt;
  std::optional<z3::expr> FuelZeroOpt;
  z3::sort fuelSort();
  z3::func_decl fuelSucc();
  z3::expr fuelZero();
  z3::expr fuelTerm(unsigned K); // Succ^K(Zero)
  static bool specIsRecursive(const VFunction *S);

  /// While emitting a recursive spec's defining axiom, self-recursive calls in
  /// the body are encoded at this (quantified) fuel variable.
  const VFunction *AxiomSelfSpec = nullptr;
  std::optional<z3::expr> AxiomSelfFuel;

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
  void setTimeoutMs(unsigned Ms) { TimeoutMs = Ms; }
  VerifyResult verifyMachine(const VCMachine &M);
  void emitSpecDefiningAxiom(const std::string &Name, const SpecAxiomContext &Ctx);
  void dumpVC(const VCExpr *E, llvm::raw_ostream &OS);
};

class Z3VerifyBackend : public VerifyBackend {
  Z3Encoder Enc;

public:
  explicit Z3VerifyBackend(unsigned TimeoutMs = 0) { Enc.setTimeoutMs(TimeoutMs); }
  llvm::StringRef getName() const override { return "z3"; }
  VerifyResult verifyPassive(const PassiveProgram &P) override;
};

} // namespace verify
} // namespace clang

#endif