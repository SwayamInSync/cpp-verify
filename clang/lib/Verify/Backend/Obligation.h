//===--- Obligation.h - Backend-neutral proof obligations --------*- C++
//-*-===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_OBLIGATION_H
#define LLVM_CLANG_VERIFY_BACKEND_OBLIGATION_H

#include "clang/Basic/SourceLocation.h"
#include "llvm/Support/Error.h"
#include <cstdint>
#include <map>
#include <memory>
#include <mutex>
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
  Heap,
  /// Finite collections of mathematical integers: a sequence, a set, a
  /// multiset (each element's multiplicity), and a map (a key domain and a
  /// value for each key in it).
  Seq,
  Set,
  Multiset,
  Map
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
  static LogicSort collection(LogicSortKind Kind);
  bool isCollection() const {
    return Kind == LogicSortKind::Seq || Kind == LogicSortKind::Set ||
           Kind == LogicSortKind::Multiset || Kind == LogicSortKind::Map;
  }
};

enum class LogicFeature : uint32_t {
  MathematicalIntegers = 1U << 0,
  BitVectors = 1U << 1,
  Pointers = 1U << 2,
  HeapArrays = 1U << 3,
  Quantifiers = 1U << 4,
  SpecFunctions = 1U << 5,
  /// Logical functions with a heap-state parameter (heap-reading specs).
  HeapFunctions = 1U << 6,
  /// Finite sequences of mathematical integers.
  Sequences = 1U << 7,
  /// Sets, multisets, and maps over all mathematical integers.
  Collections = 1U << 8,
};

/// The capability a collection sort or operation needs.
constexpr LogicFeature collectionFeature(LogicSortKind Kind) {
  return Kind == LogicSortKind::Seq ? LogicFeature::Sequences
                                    : LogicFeature::Collections;
}

enum class LogicOverflowOp { Add, Sub, Mul, Neg, SignedDiv };

/// An operation on a collection; elements, keys, values, indices, lengths,
/// and counts are mathematical integers. Each is total: an index outside a
/// sequence reads 0; a subrange clamps its bounds into the sequence; a key
/// outside a map's domain maps to 0. Sequence update and reverse are specs
/// over these, defined by the frontend.
enum class LogicCollectionOp {
  SeqEmpty,
  SeqUnit,
  SeqLength,
  SeqIndex,
  SeqPush,
  SeqSubrange,
  SeqConcat,
  SeqContains,
  SetEmpty,
  SetInsert,
  SetRemove,
  SetContains,
  SetUnion,
  SetIntersect,
  SetDifference,
  SetSubset,
  MultisetEmpty,
  MultisetInsert,
  MultisetRemove,
  MultisetCount,
  MapEmpty,
  MapInsert,
  MapRemove,
  MapContains,
  MapGet,
};

const char *logicCollectionOpName(LogicCollectionOp Op);

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
         logicFeature(LogicFeature::SpecFunctions) |
         logicFeature(LogicFeature::HeapFunctions) |
         logicFeature(LogicFeature::Sequences) |
         logicFeature(LogicFeature::Collections);
}

std::string formatLogicFeatures(LogicFeatureSet Features);
const char *logicSortName(LogicSortKind Kind);
std::string formatLogicSort(const LogicSort &Sort);

struct ObligationSource {
  std::string File;
  unsigned Line = 0;
  unsigned Column = 0;
  unsigned EndLine = 0;
  unsigned EndColumn = 0;

  bool isValid() const { return !File.empty() && Line != 0; }
  bool hasRange() const { return isValid() && EndLine != 0; }
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
    SpecCall,
    /// Children: Before, After, then Lo, Hi pairs. After equals Before at
    /// every integer address outside each [Lo, Hi).
    HeapFrame,
    /// CollectionOp applied to Children.
    Collection
  };

  Kind K;
  LogicSort Sort;
  SourceLocation Loc;
  SourceLocation EndLoc;
  ObligationSource Source;

  std::vector<std::unique_ptr<LogicExpr>> Children;
  std::string IntVal = "0";
  bool BoolVal = false;
  std::string Name;
  std::string Binder;
  LogicOverflowOp OverflowOp = LogicOverflowOp::Add;
  LogicCollectionOp CollectionOp = LogicCollectionOp::SeqEmpty;
  /// For SpecCall: function name (Args in Children).
  std::string SpecCallee;
  /// For Forall and Exists: one multi-pattern for instantiating the
  /// quantifier, a solver hint outside the term's meaning, its identity, and
  /// archives.
  std::vector<std::unique_ptr<LogicExpr>> Patterns;

  explicit LogicExpr(Kind K) : K(K) {}
};

// Compatibility name for the Z3/spec adapters while they migrate internally.
using VCExpr = LogicExpr;

/// A read of one element, member, count, or entry of a collection, which can
/// trigger a quantifier.
bool isCollectionRead(const LogicExpr &E);

/// A deep copy of \p Expr, patterns included.
std::unique_ptr<LogicExpr> cloneLogicExpr(const LogicExpr *Expr);

/// What an obligation establishes. Only Unwinding changes result semantics;
/// every other kind is diagnostic metadata.
enum class ObligationKind {
  Assertion,
  Postcondition,
  Unwinding,
  Precondition,
  InvariantEntry,
  InvariantPreserved,
  Termination,
  TypeInvariant,
  Recommends,
  Overflow,
  DivisionByZero,
  Shift,
  Bounds,
  Dereference,
  Initialization,
  PointerDifference,
  PointerValidity,
  Aliasing,
  Frame,
  Deallocation,
  MissingReturn,
  Unsupported
};

/// Public name used in obligation IDs, dumps, JSON, and Lean comments.
const char *obligationKindName(ObligationKind Kind);

enum class DiagnosticTraceKind {
  Branch,
  Call,
  Loop,
  HeapWrite,
  Allocation,
  LifetimeEnd,
  Deallocation,
  Return
};

struct DiagnosticTraceValue {
  std::string Label;
  std::unique_ptr<LogicExpr> Value;
};

struct DiagnosticTraceEvent {
  DiagnosticTraceKind Kind = DiagnosticTraceKind::Branch;
  std::string Message;
  SourceLocation Loc;
  SourceLocation EndLoc;
  ObligationSource Source;
  std::unique_ptr<LogicExpr> Guard;
  std::vector<DiagnosticTraceValue> Values;
};

struct Obligation {
  std::string Id;
  /// Source-anchored public identity. Unlike Id, this does not shift when an
  /// unrelated obligation is inserted earlier in the function.
  std::string StableId;
  ObligationKind Kind = ObligationKind::Assertion;
  SourceLocation Loc;
  SourceLocation EndLoc;
  ObligationSource Source;
  uint64_t TraceEventCount = 0;
  /// For an unsupported obligation, what the verifier does not model there.
  /// Diagnostic only: neither archived nor hashed.
  std::string Note;
  std::unique_ptr<LogicExpr> Goal;
  std::unique_ptr<LogicExpr> CounterexampleQuery;
};

struct DiagnosticVariable {
  std::string DisplayName;
  LogicSort Sort;
  SourceLocation Loc;
  SourceLocation EndLoc;
  ObligationSource Source;
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
  /// A choice function: any interpretation satisfying its axioms, which the
  /// module assumes, is its meaning. Not archived.
  bool Choice = false;
  /// An inductive predicate's body over its parameters, of which it is the
  /// least fixpoint: a counterexample check evaluates it over the arguments
  /// its derivations reach. Not archived.
  std::unique_ptr<LogicExpr> Unfolding;
  /// The postconditions over the parameters and ResultVariable, which a
  /// counterexample check may use where the definition does not settle a
  /// value; a verdict that does rests on them. Not archived.
  std::vector<std::unique_ptr<LogicExpr>> Postconditions;
  static constexpr const char *ResultVariable = "cppverify.result";
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
/// The facts beyond a module's own text that adapters gave a solver for it:
/// the inductive predicates whose unfoldings, and the specs whose
/// postconditions, a proof of the module may rest on. Shared by the copies
/// of a module, written by concurrent solves.
struct GivenFacts {
  std::mutex Lock;
  std::set<std::string> Unfoldings;
  std::set<std::string> Postconditions;
};

class ObligationModule {
public:
  std::string FunctionName;
  std::string FunctionIdentity;
  std::unique_ptr<LogicExpr> CorrectnessGoal;
  std::unique_ptr<LogicExpr> CounterexampleQuery;
  std::vector<Obligation> Obligations;
  /// Display-only source identities keyed by exact SSA name. This metadata is
  /// excluded from semantic hashes and never changes solver meaning.
  std::map<std::string, DiagnosticVariable> DiagnosticVariables;
  std::vector<DiagnosticTraceEvent> TraceEvents;
  std::map<std::string, LogicFunctionDecl> LogicFunctions;
  LogicFeatureSet RequiredFeatures = 0;
  std::string ResultVarName;
  std::string HeapPrefix;
  std::optional<BMCTransformProvenance> BMCTransform;
  /// The specs whose postconditions, and the inductive predicates whose
  /// unfoldings, the module assumes. Bookkeeping of what a proof rests on,
  /// never archived or hashed.
  std::set<std::string> AssumedPosts;
  std::set<std::string> AssumedUnfoldings;
  /// Declarations no obligation reaches that the unfoldings and
  /// postconditions above apply, for the counterexample check alone. Never
  /// encoded, archived, or hashed.
  std::map<std::string, LogicFunctionDecl> EvidenceFunctions;
  /// Never archived or hashed.
  std::shared_ptr<GivenFacts> Given = std::make_shared<GivenFacts>();
};

/// Validate every declaration, sort, call signature, obligation identity, and
/// expression in a published module. Returns the exact feature set required by
/// the validated contents.
llvm::Expected<LogicFeatureSet>
validateObligationModule(const ObligationModule &Module);

} // namespace verify
} // namespace clang

#endif