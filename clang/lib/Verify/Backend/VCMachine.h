//===--- VCMachine.h - Backend-neutral verification formulas --------------===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_VCMACHINE_H
#define LLVM_CLANG_VERIFY_BACKEND_VCMACHINE_H

#include "../IR/VExpr.h"
#include "../IR/VType.h"
#include "../Transform/Passivize.h"
#include <map>
#include <memory>
#include <set>
#include <string>
#include <vector>

namespace clang {
namespace verify {

/// Neutral logical formula for SMT, Lean export, and BMC.
class VCExpr {
public:
  enum Kind {
    True, False, IntLit, BoolLit, Var, Not, And, Or, Ite,
    Eq, Ne, Lt, Le, Gt, Ge, Add, Sub, Mul, Neg,
    Select, Store, Forall, IntToBv, BvToInt, SpecCall
  };

  Kind K;
  VIntMode IntMode = VIntMode::Machine;
  std::vector<std::unique_ptr<VCExpr>> Children;
  int64_t IntVal = 0;
  bool BoolVal = false;
  std::string Name;
  std::string Binder;
  int64_t ForallLo = 0;
  int64_t ForallHi = 0;
  /// For SpecCall: function name (Args in Children).
  std::string SpecCallee;

  explicit VCExpr(Kind K) : K(K) {}
};

class VCMachine {
public:
  std::unique_ptr<VCExpr> Goal;
  std::string ResultVarName;
  std::string HeapPrefix;
  FunctionMap SpecFunctions;
  std::map<std::string, unsigned> SpecFuel;
  std::set<std::string> HiddenSpecs;
  std::set<std::string> RevealedSpecs;
  VIntMode CallerIntMode = VIntMode::Machine;

  static VCMachine fromPassive(const PassiveProgram &P);
  static VCMachine fromVExpr(const VExpr *E, const std::string &ResultVar,
                             const std::string &CurHeap,
                             VIntMode CallerMode = VIntMode::Math);
};

} // namespace verify
} // namespace clang

#endif