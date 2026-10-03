//===--- Certify.h - Counterexamples checked against true semantics -*- C++
//-*-===//
#ifndef LLVM_CLANG_VERIFY_BACKEND_CERTIFY_H
#define LLVM_CLANG_VERIFY_BACKEND_CERTIFY_H

#include "VerifyBackend.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/StringRef.h"
#include <chrono>
#include <functional>
#include <map>
#include <memory>
#include <optional>
#include <set>
#include <string>
#include <vector>

namespace clang {
namespace verify {

/// An arbitrary-precision signed integer.
class CertInt {
  llvm::APInt Value;

  explicit CertInt(llvm::APInt Value);

public:
  CertInt();
  explicit CertInt(int64_t Value);
  static std::optional<CertInt> fromDecimal(llvm::StringRef Decimal);
  static CertInt fromBits(const llvm::APInt &Bits, bool IsSigned);
  static CertInt powerOfTwo(unsigned Exponent);

  std::string toDecimal() const;
  /// The low \p Width bits of the two's-complement representation.
  llvm::APInt bits(unsigned Width) const;
  unsigned significantBits() const { return Value.getSignificantBits(); }
  bool isNegative() const { return Value.isNegative(); }
  bool isZero() const { return Value.isZero(); }
  int compare(const CertInt &Other) const;

  CertInt operator-() const;
  friend CertInt operator+(const CertInt &L, const CertInt &R);
  friend CertInt operator-(const CertInt &L, const CertInt &R);
  friend CertInt operator*(const CertInt &L, const CertInt &R);
  /// Quotient rounded toward zero; the divisor must be nonzero.
  CertInt truncDiv(const CertInt &Divisor) const;
  /// Quotient rounded toward negative infinity; the divisor must be nonzero.
  CertInt floorDiv(const CertInt &Divisor) const;

  friend bool operator==(const CertInt &L, const CertInt &R) {
    return L.compare(R) == 0;
  }
  friend bool operator!=(const CertInt &L, const CertInt &R) {
    return L.compare(R) != 0;
  }
  friend bool operator<(const CertInt &L, const CertInt &R) {
    return L.compare(R) < 0;
  }
};

CertInt operator+(const CertInt &L, const CertInt &R);
CertInt operator-(const CertInt &L, const CertInt &R);
CertInt operator*(const CertInt &L, const CertInt &R);

/// Cells differing from the default. Equal arrays have equal representations.
/// A heap is piecewise constant: every cell from a break up to the next one
/// holds that break's value, and every cell below the first break holds
/// Default. No break repeats the value before it, so equal heaps are equal
/// representations.
struct HeapValue {
  std::map<CertInt, CertInt> Breaks;
  CertInt Default;

  void set(const CertInt &Address, const CertInt &Cell);
  /// Every cell in [Lo, Hi) holds Cell.
  void setRange(const CertInt &Lo, const CertInt &Hi, const CertInt &Cell);
  const CertInt &get(const CertInt &Address) const;
  /// Restore the no-repeated-value form after editing Breaks directly.
  void normalize();
  /// The cell-by-cell combination of L and R.
  static HeapValue
  combine(const HeapValue &L, const HeapValue &R,
          const std::function<CertInt(const CertInt &, const CertInt &)> &F);
  friend bool operator==(const HeapValue &L, const HeapValue &R) {
    return L.Default == R.Default && L.Breaks == R.Breaks;
  }
};

/// A value of a canonical logic sort. Machine integers hold their value in
/// the sort's signed or unsigned range.
struct LogicValue {
  enum class Kind { Bool, Integer, Heap, Seq, Set, Multiset, Map };
  Kind K = Kind::Bool;
  bool Truth = false;
  CertInt Integer;
  /// A heap; a set's membership (0 or 1); a multiset's counts (never
  /// negative); a map's domain (0 or 1).
  std::shared_ptr<const HeapValue> Heap;
  /// A map's values, 0 outside its domain.
  std::shared_ptr<const HeapValue> Values;
  std::shared_ptr<const std::vector<CertInt>> Elements;

  static LogicValue boolean(bool Truth);
  static LogicValue integer(CertInt Integer);
  static LogicValue heap(HeapValue Heap);
  static LogicValue sequence(std::vector<CertInt> Elements);
  static LogicValue set(HeapValue Members);
  static LogicValue multiset(HeapValue Counts);
  static LogicValue map(HeapValue Domain, HeapValue Values);
  /// A canonical rendering, usable as a key.
  std::string key() const;
  friend bool operator==(const LogicValue &L, const LogicValue &R);
};

bool operator==(const LogicValue &L, const LogicValue &R);

/// A readable rendering for diagnostics. A collection lists its elements,
/// members, or entries in order, a run of equal cells as lo..hi (a missing
/// bound is unbounded), and at most 64 items.
std::string formatLogicValue(const LogicValue &Value);

/// A solver's satisfying assignment, as the adapter's encoding reads it.
class CandidateModel {
public:
  virtual ~CandidateModel();
  /// The value of a free symbol, or nullopt when the model cannot supply it.
  virtual std::optional<LogicValue> constant(const std::string &Name,
                                             const LogicSort &Sort) = 0;
  /// The model's value of the uninterpreted pointer-validity predicate.
  virtual std::optional<bool> validPointer(const CertInt &Address) = 0;
  /// The model's value of an application of a logical function, in its
  /// result sort.
  virtual std::optional<LogicValue>
  application(const LogicFunctionDecl &Function,
              const std::vector<LogicValue> &Arguments) = 0;
  /// Whether the solver was given \p Function's whole definition, so that
  /// the model does not interpret it.
  virtual bool defined(const LogicFunctionDecl &Function) { return false; }
};

struct CertifyLimits {
  uint64_t Steps = 50000000;
  /// Nested evaluation frames; bounds native stack use.
  unsigned Frames = 50000;
  /// Binder values expanded across all bounded quantifiers.
  uint64_t QuantifierInstances = 1000000;
  /// Values tried from each end of a range too wide to expand.
  unsigned QuantifierProbe = 1024;
  /// Ranges up to this size are always expanded value by value.
  uint64_t DirectExpansion = 4096;
  unsigned MaxIntegerBits = 1U << 20;
  std::optional<std::chrono::steady_clock::time_point> Deadline;
};

/// A logical application at concrete arguments whose model value differs from
/// the value its definition gives.
struct SpecDispute {
  const LogicFunctionDecl *Function = nullptr;
  std::vector<LogicValue> Arguments;
};

enum class CertifyOutcome {
  /// The query holds under the true definitions: a real counterexample.
  Certified,
  /// The query fails under the true definitions but holds under the model's
  /// interpretation of the disputed applications.
  Disputed,
  /// The model does not satisfy the query even under its own interpretation:
  /// the adapter and the canonical semantics disagree.
  Inconsistent,
  /// The check could not be completed within its limits.
  Undetermined
};

struct CertifyResult {
  CertifyOutcome Outcome = CertifyOutcome::Undetermined;
  std::vector<SpecDispute> Disputes;
  std::string Detail;
  /// For Certified: the specs whose postconditions decided a value the
  /// definitions did not, which the counterexample rests on.
  std::set<std::string> Evidence;
  /// For Undetermined: a limit ran out while evaluating a definition.
  bool DefinitionTooDeep = false;
  /// For Undetermined: a quantifier of the query, outside every binder, whose
  /// range is too wide to expand. A model with a narrower range can be
  /// checked instead.
  const LogicExpr *WideQuantifier = nullptr;
  /// For Undetermined: an application of the query, outside every binder,
  /// whose definition is too deep to evaluate. A model with smaller
  /// arguments can be checked instead.
  const LogicExpr *DeepApplication = nullptr;
};

/// The range an adapter asks for when a model's quantifier range is too wide,
/// and how many quantifiers it narrows before giving up. The restriction only
/// selects among counterexamples: an unsat under it proves nothing.
inline constexpr unsigned NarrowedQuantifierRange = 4096;
/// The bound an adapter asks for on the integer arguments of an application
/// too deep to evaluate; like a narrowed range, it only selects among
/// counterexamples.
inline constexpr unsigned NarrowedArgumentBound = 4096;
inline constexpr unsigned MaxNarrowedQuantifiers = 8;

/// Evaluate \p Query under \p Model with every logical function at its true
/// definition, and classify the model.
CertifyResult certifyCounterexample(const ObligationModule &Module,
                                    const LogicExpr &Query,
                                    CandidateModel &Model,
                                    const CertifyLimits &Limits = {});

/// The value of \p Term under \p Model with every logical function at its
/// true definition, or nullopt with the reason in \p Failure.
std::optional<LogicValue> evaluateTerm(const ObligationModule &Module,
                                       const LogicExpr &Term,
                                       CandidateModel &Model,
                                       const CertifyLimits &Limits = {},
                                       std::string *Failure = nullptr);

/// The functions that have a definition and do not reach themselves through
/// it. An adapter can give a solver such a definition whole.
std::set<std::string> nonRecursiveDefinitions(const ObligationModule &Module);

/// A definition instance f(args) = body[args] to give a solver.
struct DefinitionInstance {
  const LogicFunctionDecl *Function = nullptr;
  std::vector<LogicValue> Arguments;
  std::string key() const;
};

/// What an adapter does after a satisfiable check.
struct RefinementDecision {
  enum class Action { Report, Refine, Stop };
  Action Next = Action::Stop;
  std::vector<DefinitionInstance> Instances;
  VerifyReason Reason = VerifyReason::None;
  std::string Message;
  /// Stopped because checking a model needed ever deeper applications, as an
  /// induction goal does; more unfolding will not settle it.
  bool Unbounded = false;
  /// Stopped although no counterexample exists.
  bool NoCounterexample = false;
};

/// Definition instances that let a solver compute the applications \p Query
/// states with closed arguments: one at each such application and at every
/// application its evaluation reaches. Hidden functions are left out, and an
/// application too deep to evaluate contributes nothing.
std::vector<DefinitionInstance>
closedApplicationInstances(const ObligationModule &Module,
                           const LogicExpr &Query,
                           const CertifyLimits &Limits = {});

/// Counterexample-guided refinement shared by the SMT adapters. Each round
/// certifies a model and answers disputed applications with instances of
/// their definitions, which are true, so a later unsat is a proof. Instances
/// of hidden functions only steer the search for a real counterexample: an
/// unsat that may rely on them is not a proof, since hide withholds the
/// definition from proofs.
class DefinitionRefinement {
  const ObligationModule &Module;
  std::set<std::string> Given;
  unsigned Rounds = 0;
  std::set<std::string> Disputed;
  std::set<std::string> HiddenGiven;
  /// Rounds whose instances were all of hidden functions: pure search.
  unsigned HiddenRounds = 0;
  const unsigned MaxHiddenRounds;

public:
  static constexpr unsigned MaxRounds = 256;
  static constexpr size_t MaxInstances = 20000;
  /// A round needing more instances than this is chasing an unbounded
  /// argument, as an induction goal makes a solver do.
  static constexpr size_t MaxRoundInstances = 2000;

  /// \p MaxHiddenRounds bounds the search among hidden functions' values,
  /// which can find a counterexample but never a proof.
  explicit DefinitionRefinement(const ObligationModule &Module,
                                unsigned MaxHiddenRounds = MaxRounds)
      : Module(Module), MaxHiddenRounds(MaxHiddenRounds) {}
  /// \p BoundedDomain: the disputes cover a domain the solver proved bounded,
  /// so a large round is exhaustive evaluation, not an unbounded chase.
  RefinementDecision next(const CertifyResult &Result,
                          bool BoundedDomain = false);
  /// The Stop decision once the solver budget or round limit runs out, or the
  /// solver gives up on a refined query; \p Detail is a parenthetical.
  RefinementDecision exhausted(llvm::StringRef Detail = {}) const;
  bool refined() const { return Rounds != 0; }
  /// Hidden instances were given, so an unsat no longer proves anything and
  /// an adapter may give the solver hidden definitions whole.
  bool searching() const { return !HiddenGiven.empty(); }
  /// The Stop decision for an unsat that may rely on hidden instances, or
  /// nullopt when the unsat is a proof.
  std::optional<RefinementDecision> unsatisfiable() const;
  const std::set<std::string> &disputedFunctions() const { return Disputed; }
};

} // namespace verify
} // namespace clang

#endif
