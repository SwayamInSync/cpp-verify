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
    Eq, Ne, Lt, Le, Gt, Ge, Add, Sub, Mul, Neg, Div, Rem,
    Select, Store, Forall, IntToBv, BvToInt, SpecCall,
    // UB safety: "the signed Op of the children does not overflow". The specific
    // VOverflowOp is stored in IntVal. Encoded via Z3 bv*_no_overflow primitives.
    NoOverflow
  };

  Kind K;
  VIntMode IntMode = VIntMode::Machine;
  /// For Div/Rem/relational ops: operands are unsigned (selects bvudiv/bvurem
  /// and unsigned comparisons in bit-vector mode).
  bool Unsigned = false;
  /// Bit-vector width for machine-int Var/IntLit/arithmetic nodes (32 or 64).
  unsigned Width = 32;
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