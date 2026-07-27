//===--- Obligation.h - Backend-neutral proof obligations --------*- C++ -*-===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_OBLIGATION_H
#define LLVM_CLANG_VERIFY_BACKEND_OBLIGATION_H

#include "../IR/VExpr.h"
#include "../IR/VType.h"
#include "../Transform/Passivize.h"
#include "clang/Basic/SourceLocation.h"
#include "llvm/Support/Error.h"
#include <cstdint>
#include <map>
#include <memory>
#include <set>
#include <string>
#include <vector>

namespace clang {
namespace verify {

enum class LogicSortKind {
  Invalid,
  Bool,
  MathematicalInteger,
  BitVector,
  Pointer,
  Heap
};

struct LogicSort {
  LogicSortKind Kind = LogicSortKind::Invalid;
  unsigned BitWidth = 0;

  static LogicSort boolSort();
  static LogicSort mathematicalInteger();
  static LogicSort bitVector(unsigned BitWidth, bool IsSigned);
  static LogicSort pointer();
  static LogicSort heap();
};

enum class LogicFeature : uint32_t {
  MathematicalIntegers = 1U << 0,
  BitVectors = 1U << 1,
  Pointers = 1U << 2,
  HeapArrays = 1U << 3,
  Quantifiers = 1U << 4,
  SpecFunctions = 1U << 5,
};

using LogicFeatureSet = uint32_t;

constexpr LogicFeatureSet logicFeature(LogicFeature Feature) {
  return static_cast<LogicFeatureSet>(Feature);
}

constexpr LogicFeatureSet allLogicFeatures() {
  return logicFeature(LogicFeature::MathematicalIntegers) |
         logicFeature(LogicFeature::BitVectors) |
         logicFeature(LogicFeature::Pointers) |
         logicFeature(LogicFeature::HeapArrays) |
         logicFeature(LogicFeature::Quantifiers) |
         logicFeature(LogicFeature::SpecFunctions);
}

std::string formatLogicFeatures(LogicFeatureSet Features);
const char *logicSortName(LogicSortKind Kind);

/// A typed logical term shared by every proof backend and IR dump.
class LogicExpr {
public:
  enum Kind {
    True,
    False,
    IntLit,
    BoolLit,
    Var,
    Not,
    And,
    Or,
    Ite,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Neg,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    BitNot,
    ValidPtr,
    Select,
    Store,
    Forall,
    Exists,
    IntToBv,
    BvToInt,
    BvResize,
    NoOverflow,
    SpecCall
  };

  Kind K;
  LogicSort Sort;
  SourceLocation Loc;

  // Transitional lowering metadata used by the existing Z3 adapter. Sort is
  // the canonical backend-facing type and is validated before publication.
  VTypeKind TypeKind = VTypeKind::Void;
  VIntMode IntMode = VIntMode::Machine;
  bool IsSigned = true;
  unsigned BitWidth = 32;
  std::vector<std::unique_ptr<LogicExpr>> Children;
  std::string IntVal = "0";
  bool BoolVal = false;
  std::string Name;
  std::string Binder;
  VOverflowOp OverflowOp = VOverflowOp::Add;
  /// For SpecCall: function name (Args in Children).
  std::string SpecCallee;

  explicit LogicExpr(Kind K) : K(K) {}
};

// Compatibility name for the Z3/spec adapters while they migrate internally.
using VCExpr = LogicExpr;

enum class ObligationKind { Assertion, Postcondition };

struct Obligation {
  std::string Id;
  ObligationKind Kind = ObligationKind::Assertion;
  SourceLocation Loc;
  std::unique_ptr<LogicExpr> CounterexampleQuery;
};

/// Canonical output of passive SSA lowering.
///
/// CounterexampleQuery is satisfiable exactly when at least one assertion can
/// fail. Obligations contain equivalent ordered queries used for diagnostics
/// and solver fallback. SpecFunctions point into the owning VFunction graph and
/// therefore have the same lifetime as the PassiveProgram's function registry.
class ObligationModule {
public:
  std::string FunctionName;
  std::string FunctionIdentity;
  std::unique_ptr<LogicExpr> CounterexampleQuery;
  std::vector<Obligation> Obligations;
  LogicFeatureSet RequiredFeatures = 0;
  std::string ResultVarName;
  std::string HeapPrefix;
  FunctionMap SpecFunctions;
  std::map<std::string, unsigned> SpecFuel;
  std::set<std::string> HiddenSpecs;
  std::set<std::string> RevealedSpecs;
  VIntMode CallerIntMode = VIntMode::Machine;
};

llvm::Expected<ObligationModule>
buildObligationModule(const PassiveProgram &Program);

llvm::Expected<std::unique_ptr<LogicExpr>>
lowerLogicExpr(const VExpr *Expr, const std::string &ResultVar,
               const std::string &CurrentHeap,
               VIntMode CallerMode = VIntMode::Math);

} // namespace verify
} // namespace clang

#endif