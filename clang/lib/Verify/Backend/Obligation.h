//===--- Obligation.h - Backend-neutral proof obligations --------*- C++
//-*-===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_OBLIGATION_H
#define LLVM_CLANG_VERIFY_BACKEND_OBLIGATION_H

#include "clang/Basic/SourceLocation.h"
#include "llvm/Support/Error.h"
#include <cstdint>
#include <map>
#include <memory>
#include <optional>
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

enum class LogicSignedness { None, Signed, Unsigned };

inline constexpr unsigned MaxLogicIntegerBitWidth = 4096;

struct LogicSort {
  LogicSortKind Kind = LogicSortKind::Invalid;
  /// Machine width for bitvectors and the originating C++ integer width for
  /// mathematical integers. Backends ignore the latter when choosing the
  /// solver sort but use it for explicit machine/mathematical conversions.
  unsigned BitWidth = 0;
  LogicSignedness Signedness = LogicSignedness::None;

  static LogicSort boolSort();
  static LogicSort mathematicalInteger(unsigned BitWidth = 32,
                                       bool IsSigned = true);
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

enum class LogicOverflowOp { Add, Sub, Mul, Neg, SignedDiv };

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

struct ObligationSource {
  std::string File;
  unsigned Line = 0;
  unsigned Column = 0;

  bool isValid() const { return !File.empty() && Line != 0; }
};

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
  ObligationSource Source;

  std::vector<std::unique_ptr<LogicExpr>> Children;
  std::string IntVal = "0";
  bool BoolVal = false;
  std::string Name;
  std::string Binder;
  LogicOverflowOp OverflowOp = LogicOverflowOp::Add;
  /// For SpecCall: function name (Args in Children).
  std::string SpecCallee;

  explicit LogicExpr(Kind K) : K(K) {}
};

// Compatibility name for the Z3/spec adapters while they migrate internally.
using VCExpr = LogicExpr;

enum class ObligationKind { Assertion, Postcondition, Unwinding };

struct Obligation {
  std::string Id;
  ObligationKind Kind = ObligationKind::Assertion;
  SourceLocation Loc;
  ObligationSource Source;
  std::unique_ptr<LogicExpr> Goal;
  std::unique_ptr<LogicExpr> CounterexampleQuery;
};

struct LogicFunctionParameter {
  std::string Name;
  LogicSort Sort;
};

/// An owned declaration for a pure logical function. DefinitionLevels contain
/// the finite, caller-visible unfoldings in the function's native result sort.
struct LogicFunctionDecl {
  std::string Identity;
  std::string DisplayName;
  std::vector<LogicFunctionParameter> Parameters;
  LogicSort ResultSort;
  unsigned DefinitionFuel = 0;
  std::unique_ptr<LogicExpr> StepDefinition;
  std::vector<std::unique_ptr<LogicExpr>> DefinitionLevels;
};

/// Semantic transform provenance that changes how verification results must be
/// interpreted. A module carrying this marker contains a finite loop unrolling,
/// so its obligations must be aggregated with BMC unwinding semantics.
struct BMCTransformProvenance {
  unsigned UnrollBound = 0;
};

/// Canonical output of passive SSA lowering.
///
/// CounterexampleQuery is satisfiable exactly when at least one assertion can
/// fail. Obligations contain equivalent ordered queries used for diagnostics
/// and solver fallback. LogicFunctions own every declaration and finite
/// definition needed by an adapter; no adapter may reach back into VCR.
class ObligationModule {
public:
  std::string FunctionName;
  std::string FunctionIdentity;
  std::unique_ptr<LogicExpr> CorrectnessGoal;
  std::unique_ptr<LogicExpr> CounterexampleQuery;
  std::vector<Obligation> Obligations;
  std::map<std::string, LogicFunctionDecl> LogicFunctions;
  LogicFeatureSet RequiredFeatures = 0;
  std::string ResultVarName;
  std::string HeapPrefix;
  std::optional<BMCTransformProvenance> BMCTransform;
};

/// Validate every declaration, sort, call signature, obligation identity, and
/// expression in a published module. Returns the exact feature set required by
/// the validated contents.
llvm::Expected<LogicFeatureSet>
validateObligationModule(const ObligationModule &Module);

} // namespace verify
} // namespace clang

#endif