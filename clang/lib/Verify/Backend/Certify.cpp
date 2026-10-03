//===--- Certify.cpp ------------------------------------------------------===//
#include "Certify.h"
#include "Presburger.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/Support/thread.h"
#include <algorithm>
#include <deque>

using namespace clang;
using namespace verify;

//===----------------------------------------------------------------------===//
// CertInt
//===----------------------------------------------------------------------===//

static llvm::APInt minimal(const llvm::APInt &Value) {
  return Value.trunc(std::max(1U, Value.getSignificantBits()));
}

CertInt::CertInt(llvm::APInt Value) : Value(minimal(Value)) {}
CertInt::CertInt() : Value(1, 0) {}
CertInt::CertInt(int64_t Value)
    : CertInt(llvm::APInt(64, static_cast<uint64_t>(Value), true)) {}

std::optional<CertInt> CertInt::fromDecimal(llvm::StringRef Decimal) {
  llvm::StringRef Digits = Decimal;
  Digits.consume_front("-");
  if (Digits.empty() ||
      !llvm::all_of(Digits, [](char C) { return C >= '0' && C <= '9'; }))
    return std::nullopt;
  const unsigned Width = static_cast<unsigned>(Digits.size()) * 4 + 2;
  return CertInt(llvm::APInt(Width, Decimal, 10));
}

CertInt CertInt::fromBits(const llvm::APInt &Bits, bool IsSigned) {
  if (IsSigned)
    return CertInt(Bits);
  return CertInt(Bits.zext(Bits.getBitWidth() + 1));
}

CertInt CertInt::powerOfTwo(unsigned Exponent) {
  return CertInt(llvm::APInt::getOneBitSet(Exponent + 2, Exponent));
}

std::string CertInt::toDecimal() const {
  llvm::SmallString<64> Text;
  Value.toString(Text, 10, /*Signed=*/true);
  return std::string(Text);
}

llvm::APInt CertInt::bits(unsigned Width) const {
  return Value.sextOrTrunc(Width);
}

int CertInt::compare(const CertInt &Other) const {
  const unsigned Width =
      std::max(Value.getBitWidth(), Other.Value.getBitWidth());
  const llvm::APInt L = Value.sext(Width);
  const llvm::APInt R = Other.Value.sext(Width);
  if (L == R)
    return 0;
  return L.slt(R) ? -1 : 1;
}

CertInt CertInt::operator-() const {
  llvm::APInt Wide = Value.sext(Value.getBitWidth() + 1);
  Wide.negate();
  return CertInt(Wide);
}

CertInt verify::operator+(const CertInt &L, const CertInt &R) {
  const unsigned Width =
      std::max(L.Value.getBitWidth(), R.Value.getBitWidth()) + 1;
  return CertInt(L.Value.sext(Width) + R.Value.sext(Width));
}

CertInt verify::operator-(const CertInt &L, const CertInt &R) {
  const unsigned Width =
      std::max(L.Value.getBitWidth(), R.Value.getBitWidth()) + 1;
  return CertInt(L.Value.sext(Width) - R.Value.sext(Width));
}

CertInt verify::operator*(const CertInt &L, const CertInt &R) {
  const unsigned Width = L.Value.getBitWidth() + R.Value.getBitWidth();
  return CertInt(L.Value.sext(Width) * R.Value.sext(Width));
}

CertInt CertInt::truncDiv(const CertInt &Divisor) const {
  const unsigned Width =
      std::max(Value.getBitWidth(), Divisor.Value.getBitWidth()) + 1;
  return CertInt(Value.sext(Width).sdiv(Divisor.Value.sext(Width)));
}

CertInt CertInt::floorDiv(const CertInt &Divisor) const {
  CertInt Quotient = truncDiv(Divisor);
  if (*this - Quotient * Divisor != CertInt() &&
      isNegative() != Divisor.isNegative())
    return Quotient - CertInt(1);
  return Quotient;
}

//===----------------------------------------------------------------------===//
// Values
//===----------------------------------------------------------------------===//

void HeapValue::set(const CertInt &Address, const CertInt &Cell) {
  setRange(Address, Address + CertInt(1), Cell);
}

void HeapValue::setRange(const CertInt &Lo, const CertInt &Hi,
                         const CertInt &Cell) {
  if (!(Lo < Hi))
    return;
  const CertInt After = get(Hi);
  Breaks.erase(Breaks.lower_bound(Lo), Breaks.upper_bound(Hi));
  Breaks[Lo] = Cell;
  Breaks[Hi] = After;
  normalize();
}

const CertInt &HeapValue::get(const CertInt &Address) const {
  auto It = Breaks.upper_bound(Address);
  if (It == Breaks.begin())
    return Default;
  return std::prev(It)->second;
}

void HeapValue::normalize() {
  const CertInt *Previous = &Default;
  for (auto It = Breaks.begin(); It != Breaks.end();) {
    if (It->second == *Previous) {
      It = Breaks.erase(It);
      continue;
    }
    Previous = &It->second;
    ++It;
  }
}

LogicValue LogicValue::boolean(bool Truth) {
  LogicValue Value;
  Value.K = Kind::Bool;
  Value.Truth = Truth;
  return Value;
}

LogicValue LogicValue::integer(CertInt Integer) {
  LogicValue Value;
  Value.K = Kind::Integer;
  Value.Integer = std::move(Integer);
  return Value;
}

LogicValue LogicValue::heap(HeapValue Heap) {
  LogicValue Value;
  Value.K = Kind::Heap;
  Value.Heap = std::make_shared<const HeapValue>(std::move(Heap));
  return Value;
}

LogicValue LogicValue::sequence(std::vector<CertInt> Elements) {
  LogicValue Value;
  Value.K = Kind::Seq;
  Value.Elements =
      std::make_shared<const std::vector<CertInt>>(std::move(Elements));
  return Value;
}

LogicValue LogicValue::set(HeapValue Members) {
  LogicValue Value;
  Value.K = Kind::Set;
  Members = HeapValue::combine(
      Members, Members, [](const CertInt &C, const CertInt &) {
        return CertInt(C.isZero() ? 0 : 1);
      });
  Value.Heap = std::make_shared<const HeapValue>(std::move(Members));
  return Value;
}

LogicValue LogicValue::multiset(HeapValue Counts) {
  LogicValue Value;
  Value.K = Kind::Multiset;
  Counts = HeapValue::combine(Counts, Counts,
                              [](const CertInt &C, const CertInt &) {
                                return C.isNegative() ? CertInt(0) : C;
                              });
  Value.Heap = std::make_shared<const HeapValue>(std::move(Counts));
  return Value;
}

LogicValue LogicValue::map(HeapValue Domain, HeapValue Values) {
  LogicValue Value;
  Value.K = Kind::Map;
  Domain = HeapValue::combine(Domain, Domain,
                              [](const CertInt &C, const CertInt &) {
                                return CertInt(C.isZero() ? 0 : 1);
                              });
  // A key outside the domain maps to 0, whatever a representation holds.
  Values = HeapValue::combine(Domain, Values,
                              [](const CertInt &In, const CertInt &V) {
                                return In.isZero() ? CertInt(0) : V;
                              });
  Value.Heap = std::make_shared<const HeapValue>(std::move(Domain));
  Value.Values = std::make_shared<const HeapValue>(std::move(Values));
  return Value;
}

HeapValue HeapValue::combine(
    const HeapValue &L, const HeapValue &R,
    const std::function<CertInt(const CertInt &, const CertInt &)> &F) {
  HeapValue Out;
  Out.Default = F(L.Default, R.Default);
  std::set<CertInt> Points;
  for (const auto &Break : L.Breaks)
    Points.insert(Break.first);
  for (const auto &Break : R.Breaks)
    Points.insert(Break.first);
  for (const CertInt &Point : Points)
    Out.Breaks[Point] = F(L.get(Point), R.get(Point));
  Out.normalize();
  return Out;
}

std::string LogicValue::key() const {
  switch (K) {
  case Kind::Bool:
    return Truth ? "true" : "false";
  case Kind::Integer:
    return Integer.toDecimal();
  case Kind::Heap:
  case Kind::Set:
  case Kind::Multiset:
  case Kind::Map: {
    auto text = [](const HeapValue &Cells) {
      std::string Text = "[" + Cells.Default.toDecimal();
      for (const auto &[Address, Cell] : Cells.Breaks)
        Text += ";" + Address.toDecimal() + ":" + Cell.toDecimal();
      return Text + "]";
    };
    std::string Text = text(*Heap);
    if (K == Kind::Map)
      Text += text(*Values);
    return Text;
  }
  case Kind::Seq: {
    std::string Text = "<";
    for (const CertInt &Element : *Elements)
      Text += Element.toDecimal() + ",";
    return Text + ">";
  }
  }
  return {};
}

std::string verify::formatLogicValue(const LogicValue &Value) {
  constexpr size_t Shown = 64;
  // Maximal runs of equal cells across the heaps, in address order; a
  // missing bound is unbounded.
  struct Run {
    std::optional<CertInt> Lo, Hi;
    std::vector<CertInt> Cells;
  };
  auto runs = [](std::vector<const HeapValue *> Heaps) {
    std::set<CertInt> Points;
    for (const HeapValue *Heap : Heaps)
      for (const auto &Break : Heap->Breaks)
        Points.insert(Break.first);
    std::vector<Run> Runs;
    auto add = [&](std::optional<CertInt> Lo, std::vector<CertInt> Cells) {
      if (!Runs.empty() && Runs.back().Cells == Cells)
        return;
      if (!Runs.empty())
        Runs.back().Hi = *Lo - CertInt(1);
      Runs.push_back({std::move(Lo), std::nullopt, std::move(Cells)});
    };
    std::vector<CertInt> Defaults;
    for (const HeapValue *Heap : Heaps)
      Defaults.push_back(Heap->Default);
    add(std::nullopt, Defaults);
    for (const CertInt &Point : Points) {
      std::vector<CertInt> Cells;
      for (const HeapValue *Heap : Heaps)
        Cells.push_back(Heap->get(Point));
      add(Point, std::move(Cells));
    }
    return Runs;
  };
  auto range = [](const Run &R) {
    if (R.Lo && R.Hi && *R.Lo == *R.Hi)
      return R.Lo->toDecimal();
    return (R.Lo ? R.Lo->toDecimal() : std::string()) + ".." +
           (R.Hi ? R.Hi->toDecimal() : std::string());
  };
  auto join = [&](const std::vector<std::string> &Items, const char *Open,
                  const char *Close) {
    std::string Text = Open;
    for (size_t I = 0; I != Items.size() && I != Shown; ++I)
      Text += (I ? ", " : "") + Items[I];
    if (Items.size() > Shown)
      Text += ", ... (" + std::to_string(Items.size() - Shown) + " more)";
    return Text + Close;
  };
  std::vector<std::string> Items;
  switch (Value.K) {
  case LogicValue::Kind::Bool:
  case LogicValue::Kind::Integer:
    return Value.key();
  case LogicValue::Kind::Heap:
    for (const Run &R : runs({Value.Heap.get()}))
      Items.push_back(range(R) + ": " + R.Cells[0].toDecimal());
    return join(Items, "{", "}");
  case LogicValue::Kind::Seq:
    for (const CertInt &Element : *Value.Elements)
      Items.push_back(Element.toDecimal());
    return join(Items, "[", "]");
  case LogicValue::Kind::Set:
    for (const Run &R : runs({Value.Heap.get()}))
      if (!R.Cells[0].isZero())
        Items.push_back(range(R));
    return join(Items, "{", "}");
  case LogicValue::Kind::Multiset:
    for (const Run &R : runs({Value.Heap.get()}))
      if (!R.Cells[0].isZero())
        Items.push_back(range(R) + ": " + R.Cells[0].toDecimal());
    return join(Items, "{", "}");
  case LogicValue::Kind::Map:
    for (const Run &R : runs({Value.Heap.get(), Value.Values.get()}))
      if (!R.Cells[0].isZero())
        Items.push_back(range(R) + " -> " + R.Cells[1].toDecimal());
    return join(Items, "{", "}");
  }
  return {};
}

bool verify::operator==(const LogicValue &L, const LogicValue &R) {
  if (L.K != R.K)
    return false;
  switch (L.K) {
  case LogicValue::Kind::Bool:
    return L.Truth == R.Truth;
  case LogicValue::Kind::Integer:
    return L.Integer == R.Integer;
  case LogicValue::Kind::Heap:
  case LogicValue::Kind::Set:
  case LogicValue::Kind::Multiset:
    return *L.Heap == *R.Heap;
  case LogicValue::Kind::Map:
    return *L.Heap == *R.Heap && *L.Values == *R.Values;
  case LogicValue::Kind::Seq:
    return *L.Elements == *R.Elements;
  }
  return false;
}

CandidateModel::~CandidateModel() = default;

std::string DefinitionInstance::key() const {
  std::string Key = Of == Kind::Definition  ? "D"
                    : Of == Kind::Unfolding ? "U"
                                            : "P";
  Key += Function ? Function->Identity : std::string();
  for (const LogicValue &Argument : Arguments)
    Key += "\x1f" + Argument.key();
  return Key;
}

//===----------------------------------------------------------------------===//
// Canonical semantics
//===----------------------------------------------------------------------===//

namespace {

bool isSigned(const LogicSort &Sort) {
  return Sort.Signedness == LogicSignedness::Signed;
}

bool isInteger(const LogicSort &Sort) {
  return Sort.Kind == LogicSortKind::MathematicalInteger ||
         Sort.Kind == LogicSortKind::Pointer;
}

CertInt reduce(const CertInt &Value, const LogicSort &Sort) {
  return CertInt::fromBits(Value.bits(Sort.BitWidth), isSigned(Sort));
}

bool inRange(const CertInt &Value, unsigned Width, bool Signed) {
  if (Signed) {
    const CertInt Half = CertInt::powerOfTwo(Width - 1);
    return !(Value < -Half) && Value < Half;
  }
  return !Value.isNegative() && Value < CertInt::powerOfTwo(Width);
}

/// The same w bits read under another signedness.
CertInt reinterpret(const CertInt &Value, unsigned Width, bool FromSigned,
                    bool ToSigned) {
  if (FromSigned == ToSigned)
    return Value;
  if (FromSigned)
    return Value.isNegative() ? Value + CertInt::powerOfTwo(Width) : Value;
  return Value < CertInt::powerOfTwo(Width - 1)
             ? Value
             : Value - CertInt::powerOfTwo(Width);
}

/// Width and signedness change between machine sorts, as BvResize.
CertInt convertMachine(const CertInt &Value, const LogicSort &Source,
                       const LogicSort &Target) {
  if (Target.BitWidth == Source.BitWidth)
    return reinterpret(Value, Target.BitWidth, isSigned(Source),
                       isSigned(Target));
  if (Target.BitWidth < Source.BitWidth)
    return reduce(Value, Target);
  if (isSigned(Source) && !isSigned(Target) && Value.isNegative())
    return Value + CertInt::powerOfTwo(Target.BitWidth);
  return Value;
}

std::string displayName(const LogicFunctionDecl &Function) {
  return Function.DisplayName.empty() ? Function.Identity
                                      : Function.DisplayName;
}

enum class View { Definitions, Model };

class Evaluator {
  const ObligationModule &Module;
  CandidateModel &Model;
  const CertifyLimits &Limits;
  const View Mode;
  uint64_t Steps = 0;
  unsigned Frames = 0;
  uint64_t Instances = 0;
  std::vector<const LogicFunctionDecl *> Active;
  bool LimitInDefinition = false;
  const LogicExpr *Wide = nullptr;
  const LogicExpr *Deep = nullptr;
  std::string Failure;
  std::vector<std::pair<std::string, LogicValue>> Scope;
  /// Definitions see only their own parameters.
  size_t ScopeBase = 0;
  std::map<std::string, LogicValue> Constants;
  /// A least fixpoint's values over the arguments its derivations reach,
  /// and the applications each node's unfolding read.
  struct FixpointGraph {
    std::vector<std::pair<const LogicFunctionDecl *, std::vector<LogicValue>>>
        Nodes;
    std::vector<bool> Values;
    std::vector<std::set<size_t>> Reads;
  };
  /// A computed application and how it was decided: by a fixpoint, by a
  /// proved postcondition, or by the definition.
  struct Computed {
    LogicValue Value;
    std::shared_ptr<const FixpointGraph> Graph;
    size_t Node = 0;
    bool ByPostcondition = false;
  };
  std::map<std::string, Computed> Applications;
  std::vector<SpecDispute> Disputes;
  std::set<std::string> DisputeKeys;
  std::vector<DefinitionInstance> Evaluated;
  /// The specs whose postconditions decided a value.
  std::set<std::string> Evidence;
  /// Applications whose definitions could not be decided, and why: tried
  /// once.
  std::map<std::string, std::string> Undecided;
  /// Applications whose definitions are being evaluated.
  std::set<std::string> InProgress;
  /// The time or step budget is spent: no failure is recovered from.
  bool Exhausted = false;
  /// The step at which the slice of the innermost fair search ends.
  uint64_t SliceEnd = UINT64_MAX;
  /// That slice ran out: the failure says nothing of the term, and only
  /// the search that gave the slice recovers from it.
  bool SliceSpent = false;
  static constexpr uint64_t FirstSlice = 4096;
  static constexpr uint64_t LeastSlice = 64;
  uint64_t NextClockCheck = 4096;
  /// Functions whose postconditions are being evaluated as evidence.
  std::set<std::string> PostsInUse;
  std::optional<std::set<std::string>> NonRecursive;

  /// The least fixpoint of an inductive predicate's group over the
  /// arguments its derivations reach: every value starts false and becomes
  /// true once its unfolding holds; a value that changes wakes those that
  /// read it.
  struct Fixpoint {
    std::set<std::string> Group;
    std::map<std::string, size_t> Index;
    std::vector<std::pair<const LogicFunctionDecl *, std::vector<LogicValue>>>
        Nodes;
    std::vector<bool> Values;
    std::vector<std::set<size_t>> Readers;
    std::vector<std::set<size_t>> Reads;
    std::deque<size_t> Pending;
    size_t Reader = 0;
  };
  std::vector<Fixpoint *> Fixpoints;
  static constexpr size_t MaxFixpointArguments = 1024;
  /// Terms a quantifier body may grow to by unfolding definitions.
  static constexpr uint64_t MaxUnfoldedTerms = 20000;

  std::nullopt_t fail(std::string Message) {
    if (Failure.empty())
      Failure = std::move(Message);
    return std::nullopt;
  }

  /// A budget ran out: the failure is not the term's, so nothing below the
  /// search that set the budget may recover from it.
  bool spent() const { return Exhausted || SliceSpent; }

  /// Runs \p Count tries fairly: each gets a slice of evaluation steps in
  /// turn, the slices doubling every round, so whichever settles cheaply is
  /// found whatever the order. true: some try returned \p Wanted; false:
  /// every try returned the other value; nullopt: neither, with the failure
  /// of the first try that could not be decided.
  std::optional<bool>
  fairly(size_t Count, llvm::function_ref<std::optional<bool>(size_t)> Try,
         bool Wanted) {
    struct State {
      std::string Failure;
      bool LimitInDefinition;
      const LogicExpr *Deep;
      const LogicExpr *Wide;
    };
    const State Saved{"", LimitInDefinition, Deep, Wide};
    auto restore = [&](const State &To) {
      Failure = To.Failure;
      LimitInDefinition = To.LimitInDefinition;
      Deep = To.Deep;
      Wide = To.Wide;
    };
    const uint64_t OuterEnd = SliceEnd;
    std::optional<State> First;
    std::vector<size_t> Pending(Count);
    for (size_t I = 0; I != Count; ++I)
      Pending[I] = I;
    for (uint64_t Slice = FirstSlice; !Pending.empty(); Slice *= 2) {
      std::vector<size_t> Again;
      for (size_t At = 0; At != Pending.size(); ++At) {
        const size_t Index = Pending[At];
        // Within a slice the tries left share what remains of it, so a
        // search nested in a try still reaches its later tries, and a try
        // after cheap ones gets nearly all of it.
        uint64_t Mine = Slice;
        if (OuterEnd != UINT64_MAX)
          Mine = std::clamp<uint64_t>(
              (OuterEnd > Steps ? OuterEnd - Steps : 0) / (Pending.size() - At),
              LeastSlice, Slice);
        SliceSpent = false;
        SliceEnd = std::min(OuterEnd, Steps + Mine);
        std::optional<bool> Holds = Try(Index);
        SliceEnd = OuterEnd;
        if (Holds) {
          // A value is exact even where a slice ran out below it.
          if (!Exhausted) {
            SliceSpent = false;
            restore(Saved);
          }
          if (*Holds == Wanted)
            return true;
          continue;
        }
        if (Exhausted || (SliceSpent && OuterEnd < Steps))
          return std::nullopt;
        if (SliceSpent)
          Again.push_back(Index);
        else if (!First)
          First = State{Failure, LimitInDefinition, Deep, Wide};
        SliceSpent = false;
        restore(Saved);
      }
      Pending = std::move(Again);
    }
    if (First) {
      restore(*First);
      return std::nullopt;
    }
    return false;
  }

  /// \p Body at the binder values \p At(0), ..., \p At(Count - 1),
  /// searched fairly for one where it is not \p Forall, which decides the
  /// quantifier. false: it is \p Forall at every one.
  std::optional<bool> decidingInstance(const LogicExpr *Body,
                                       const std::string &Binder, size_t Count,
                                       llvm::function_ref<CertInt(size_t)> At,
                                       bool Forall) {
    return fairly(
        Count,
        [&](size_t I) {
          ++Instances;
          Scope.emplace_back(Binder, LogicValue::integer(At(I)));
          std::optional<bool> Holds = truthOf(Body);
          Scope.pop_back();
          return Holds;
        },
        !Forall);
  }

  std::optional<bool> decidingInstance(const LogicExpr *Body,
                                       const std::string &Binder,
                                       const std::vector<CertInt> &Binders,
                                       bool Forall) {
    return decidingInstance(
        Body, Binder, Binders.size(), [&](size_t I) { return Binders[I]; },
        Forall);
  }

  /// A quantifier over \p Binders that covers its range: decided by the
  /// instance that is not \p Forall, else \p Forall.
  std::optional<LogicValue> overBinders(const LogicExpr *Body,
                                        const std::string &Binder,
                                        const std::vector<CertInt> &Binders,
                                        bool Forall) {
    std::optional<bool> Decided =
        decidingInstance(Body, Binder, Binders, Forall);
    if (!Decided)
      return std::nullopt;
    return LogicValue::boolean(*Decided ? !Forall : Forall);
  }

  std::nullopt_t limit(std::string Message) {
    if (Failure.empty() && !Active.empty()) {
      LimitInDefinition = true;
      Message += " while evaluating " + displayName(*Active.back());
    }
    return fail(std::move(Message));
  }

  std::optional<LogicValue> integer(CertInt Value) {
    if (Value.significantBits() > Limits.MaxIntegerBits)
      return limit("an integer exceeds " +
                   std::to_string(Limits.MaxIntegerBits) + " bits");
    return LogicValue::integer(std::move(Value));
  }

  std::optional<CertInt> integerOf(const LogicExpr *E) {
    std::optional<LogicValue> Value = eval(E);
    if (!Value)
      return std::nullopt;
    if (Value->K != LogicValue::Kind::Integer)
      return fail("an integer term has a non-integer value");
    return Value->Integer;
  }

  std::optional<bool> truthOf(const LogicExpr *E) {
    std::optional<LogicValue> Value = eval(E);
    if (!Value)
      return std::nullopt;
    if (Value->K == LogicValue::Kind::Bool)
      return Value->Truth;
    if (Value->K == LogicValue::Kind::Integer)
      return !Value->Integer.isZero();
    return fail("a condition has a heap value");
  }

  std::optional<LogicValue> coerce(std::optional<LogicValue> Value,
                                   const LogicSort &Source,
                                   const LogicSort &Target, bool IsSigned) {
    if (!Value)
      return std::nullopt;
    switch (Target.Kind) {
    case LogicSortKind::Bool:
      if (Value->K == LogicValue::Kind::Bool)
        return Value;
      if (Value->K == LogicValue::Kind::Integer)
        return LogicValue::boolean(!Value->Integer.isZero());
      break;
    case LogicSortKind::Heap:
      if (Value->K == LogicValue::Kind::Heap)
        return Value;
      break;
    case LogicSortKind::Seq:
      if (Value->K == LogicValue::Kind::Seq)
        return Value;
      break;
    case LogicSortKind::Set:
      if (Value->K == LogicValue::Kind::Set)
        return Value;
      break;
    case LogicSortKind::Multiset:
      if (Value->K == LogicValue::Kind::Multiset)
        return Value;
      break;
    case LogicSortKind::Map:
      if (Value->K == LogicValue::Kind::Map)
        return Value;
      break;
    case LogicSortKind::BitVector:
      if (Value->K != LogicValue::Kind::Integer)
        break;
      if (Source.Kind == LogicSortKind::BitVector) {
        if (Source.BitWidth != Target.BitWidth)
          break;
        return LogicValue::integer(reinterpret(Value->Integer, Target.BitWidth,
                                               isSigned(Source),
                                               isSigned(Target)));
      }
      if (isInteger(Source))
        return LogicValue::integer(reduce(Value->Integer, Target));
      break;
    case LogicSortKind::MathematicalInteger:
    case LogicSortKind::Pointer:
      if (Value->K != LogicValue::Kind::Integer)
        break;
      if (Source.Kind == LogicSortKind::BitVector)
        return LogicValue::integer(reinterpret(Value->Integer, Source.BitWidth,
                                               isSigned(Source), IsSigned));
      if (isInteger(Source))
        return Value;
      break;
    case LogicSortKind::Invalid:
      break;
    }
    return fail("unsupported sort conversion from " + formatLogicSort(Source) +
                " to " + formatLogicSort(Target));
  }

  std::optional<LogicValue> lookup(const LogicExpr *E) {
    for (size_t I = Scope.size(); I > ScopeBase; --I)
      if (Scope[I - 1].first == E->Name)
        return Scope[I - 1].second;
    if (ScopeBase != 0)
      return fail("a definition refers to " + E->Name +
                  ", which is not a parameter");
    if (auto It = Constants.find(E->Name); It != Constants.end())
      return It->second;
    std::optional<LogicValue> Value = Model.constant(E->Name, E->Sort);
    if (!Value)
      return fail("the model gives no value for " + E->Name);
    auto collectionKind = [](LogicSortKind Kind) {
      switch (Kind) {
      case LogicSortKind::Seq:
        return LogicValue::Kind::Seq;
      case LogicSortKind::Set:
        return LogicValue::Kind::Set;
      case LogicSortKind::Multiset:
        return LogicValue::Kind::Multiset;
      default:
        return LogicValue::Kind::Map;
      }
    };
    const bool Matches = E->Sort.Kind == LogicSortKind::Heap
                             ? Value->K == LogicValue::Kind::Heap
                         : E->Sort.isCollection()
                             ? Value->K == collectionKind(E->Sort.Kind)
                         : E->Sort.Kind == LogicSortKind::Bool
                             ? Value->K == LogicValue::Kind::Bool
                             : Value->K == LogicValue::Kind::Integer &&
                                   (E->Sort.Kind != LogicSortKind::BitVector ||
                                    inRange(Value->Integer, E->Sort.BitWidth,
                                            isSigned(E->Sort)));
    if (!Matches)
      return fail("the model value of " + E->Name + " is not in its sort " +
                  formatLogicSort(E->Sort));
    Constants.emplace(E->Name, *Value);
    return Value;
  }

  std::optional<LogicValue>
  machineArithmetic(const LogicExpr *E, const CertInt &L, const CertInt &R) {
    const LogicSort &Sort = E->Sort;
    const unsigned Width = Sort.BitWidth;
    const bool Signed = isSigned(Sort);
    switch (E->K) {
    case LogicExpr::Add:
      return LogicValue::integer(reduce(L + R, Sort));
    case LogicExpr::Sub:
      return LogicValue::integer(reduce(L - R, Sort));
    case LogicExpr::Mul:
      return LogicValue::integer(reduce(L * R, Sort));
    // Zero divisors follow SMT-LIB, as both machine encodings do.
    case LogicExpr::Div:
      if (R.isZero()) {
        if (!Signed)
          return LogicValue::integer(CertInt::powerOfTwo(Width) - CertInt(1));
        return LogicValue::integer(L.isNegative() ? reduce(CertInt(1), Sort)
                                                  : CertInt(-1));
      }
      return LogicValue::integer(reduce(L.truncDiv(R), Sort));
    case LogicExpr::Rem:
      if (R.isZero())
        return LogicValue::integer(L);
      return LogicValue::integer(L - R * L.truncDiv(R));
    case LogicExpr::BitAnd:
      return LogicValue::integer(
          CertInt::fromBits(L.bits(Width) & R.bits(Width), Signed));
    case LogicExpr::BitOr:
      return LogicValue::integer(
          CertInt::fromBits(L.bits(Width) | R.bits(Width), Signed));
    case LogicExpr::BitXor:
      return LogicValue::integer(
          CertInt::fromBits(L.bits(Width) ^ R.bits(Width), Signed));
    case LogicExpr::Shl:
    case LogicExpr::Shr: {
      // The amount is read as an unsigned w-bit pattern.
      const llvm::APInt Amount = R.bits(Width);
      if (Amount.uge(Width)) {
        if (E->K == LogicExpr::Shl || !Signed || !L.isNegative())
          return LogicValue::integer(CertInt());
        return LogicValue::integer(CertInt(-1));
      }
      const CertInt Scale =
          CertInt::powerOfTwo(static_cast<unsigned>(Amount.getZExtValue()));
      if (E->K == LogicExpr::Shl)
        return LogicValue::integer(reduce(L * Scale, Sort));
      return LogicValue::integer(L.floorDiv(Scale));
    }
    default:
      return fail("unsupported machine-integer operator");
    }
  }

  std::optional<LogicValue> binary(const LogicExpr *E) {
    std::optional<LogicValue> Left = eval(E->Children[0].get());
    if (!Left)
      return std::nullopt;
    std::optional<LogicValue> Right = eval(E->Children[1].get());
    if (!Right)
      return std::nullopt;
    if (E->K == LogicExpr::Eq || E->K == LogicExpr::Ne) {
      if (Left->K != Right->K)
        return fail("an equality compares values of different kinds");
      return LogicValue::boolean((*Left == *Right) == (E->K == LogicExpr::Eq));
    }
    if (Left->K != LogicValue::Kind::Integer ||
        Right->K != LogicValue::Kind::Integer)
      return fail("an arithmetic operand is not an integer");
    const CertInt &L = Left->Integer;
    const CertInt &R = Right->Integer;
    switch (E->K) {
    case LogicExpr::Lt:
      return LogicValue::boolean(L < R);
    case LogicExpr::Le:
      return LogicValue::boolean(!(R < L));
    case LogicExpr::Gt:
      return LogicValue::boolean(R < L);
    case LogicExpr::Ge:
      return LogicValue::boolean(!(L < R));
    default:
      break;
    }
    if (E->Sort.Kind == LogicSortKind::BitVector)
      return machineArithmetic(E, L, R);
    switch (E->K) {
    case LogicExpr::Add:
      return integer(L + R);
    case LogicExpr::Sub:
      return integer(L - R);
    case LogicExpr::Mul:
      return integer(L * R);
    // Mathematical division truncates; a zero divisor gives quotient 0 and
    // remainder equal to the dividend.
    case LogicExpr::Div:
      return integer(R.isZero() ? CertInt() : L.truncDiv(R));
    case LogicExpr::Rem:
      return integer(R.isZero() ? L : L - R * L.truncDiv(R));
    default:
      return fail("unsupported mathematical operator");
    }
  }

  std::optional<LogicValue> noOverflow(const LogicExpr *E) {
    const LogicSort Checked =
        LogicSort::bitVector(E->Children[0]->Sort.BitWidth, true);
    std::vector<CertInt> Operands;
    for (const auto &Child : E->Children) {
      std::optional<CertInt> Value = integerOf(Child.get());
      if (!Value)
        return std::nullopt;
      Operands.push_back(convertMachine(*Value, Child->Sort, Checked));
    }
    const unsigned Width = Checked.BitWidth;
    auto fits = [&](const CertInt &Value) {
      return LogicValue::boolean(inRange(Value, Width, true));
    };
    if (E->OverflowOp == LogicOverflowOp::Neg)
      return fits(-Operands[0]);
    switch (E->OverflowOp) {
    case LogicOverflowOp::Add:
      return fits(Operands[0] + Operands[1]);
    case LogicOverflowOp::Sub:
      return fits(Operands[0] - Operands[1]);
    case LogicOverflowOp::Mul:
      return fits(Operands[0] * Operands[1]);
    case LogicOverflowOp::SignedDiv:
      return LogicValue::boolean(
          !(Operands[0] == -CertInt::powerOfTwo(Width - 1) &&
            Operands[1] == CertInt(-1)));
    case LogicOverflowOp::Neg:
      break;
    }
    return fail("unsupported overflow predicate");
  }

  static bool mentions(const LogicExpr *E, const std::string &Binder) {
    if (E->K == LogicExpr::Var)
      return E->Name == Binder;
    return llvm::any_of(E->Children,
                        [&](const std::unique_ptr<LogicExpr> &Child) {
                          return mentions(Child.get(), Binder);
                        });
  }

  /// Built from the binder by exact integer +, -, negation, and scaling.
  static bool affineIn(const LogicExpr *E, const std::string &Binder) {
    if (!mentions(E, Binder))
      return true;
    if (!isInteger(E->Sort))
      return false;
    switch (E->K) {
    case LogicExpr::Var:
      return true;
    case LogicExpr::Add:
    case LogicExpr::Sub:
      return affineIn(E->Children[0].get(), Binder) &&
             affineIn(E->Children[1].get(), Binder);
    case LogicExpr::Neg:
      return affineIn(E->Children[0].get(), Binder);
    case LogicExpr::Mul:
      return (!mentions(E->Children[0].get(), Binder) &&
              affineIn(E->Children[1].get(), Binder)) ||
             (!mentions(E->Children[1].get(), Binder) &&
              affineIn(E->Children[0].get(), Binder));
    default:
      return false;
    }
  }

  /// A comparison operand that is binder-free, affine in the binder, or such
  /// a term converted to a machine sort.
  static bool comparesAffine(const LogicExpr *E, const std::string &Binder) {
    if (!mentions(E, Binder))
      return true;
    if (E->K == LogicExpr::IntToBv)
      E = E->Children[0].get();
    return isInteger(E->Sort) && affineIn(E, Binder);
  }

  /// Built from the binder by +, -, negation, products, and conversions:
  /// exact integer ones, and machine ones, which must not wrap over the range.
  static bool polynomialIn(const LogicExpr *E, const std::string &Binder) {
    if (!mentions(E, Binder))
      return true;
    const bool Machine = E->Sort.Kind == LogicSortKind::BitVector;
    if (!isInteger(E->Sort) && !Machine)
      return false;
    switch (E->K) {
    case LogicExpr::Var:
      return !Machine;
    case LogicExpr::Add:
    case LogicExpr::Sub:
    case LogicExpr::Mul:
      return polynomialIn(E->Children[0].get(), Binder) &&
             polynomialIn(E->Children[1].get(), Binder);
    case LogicExpr::Neg:
    case LogicExpr::IntToBv:
    case LogicExpr::BvToInt:
    case LogicExpr::BvResize:
      return polynomialIn(E->Children[0].get(), Binder);
    default:
      return false;
    }
  }

  static bool comparesPolynomial(const LogicExpr *E,
                                 const std::string &Binder) {
    return polynomialIn(E, Binder);
  }

  static constexpr unsigned MaxPolynomialDegree = 8;
  /// Intervals examined while isolating the sign changes of one comparison.
  static constexpr unsigned MaxIsolationSteps = 20000;

  using Polynomial = std::vector<CertInt>;

  /// The coefficients, lowest degree first, of a polynomial in the binder.
  /// Each machine operation or conversion adds its value to \p Fit: it equals
  /// the exact one only where that stays within its sort.
  std::optional<Polynomial>
  polynomialOf(const LogicExpr *E, const std::string &Binder,
               std::vector<std::pair<Polynomial, LogicSort>> &Fit) {
    if (!mentions(E, Binder)) {
      std::optional<CertInt> Value = integerOf(E);
      if (!Value)
        return std::nullopt;
      return Polynomial{*Value};
    }
    std::optional<Polynomial> Result;
    switch (E->K) {
    case LogicExpr::Var:
      return Polynomial{CertInt(0), CertInt(1)};
    case LogicExpr::BvToInt:
      return polynomialOf(E->Children[0].get(), Binder, Fit);
    case LogicExpr::IntToBv:
    case LogicExpr::BvResize:
      Result = polynomialOf(E->Children[0].get(), Binder, Fit);
      break;
    case LogicExpr::Neg:
      Result = polynomialOf(E->Children[0].get(), Binder, Fit);
      if (Result)
        for (CertInt &Coefficient : *Result)
          Coefficient = -Coefficient;
      break;
    case LogicExpr::Add:
    case LogicExpr::Sub:
    case LogicExpr::Mul: {
      std::optional<Polynomial> L =
          polynomialOf(E->Children[0].get(), Binder, Fit);
      std::optional<Polynomial> R =
          L ? polynomialOf(E->Children[1].get(), Binder, Fit) : std::nullopt;
      if (!R)
        return std::nullopt;
      if (E->K == LogicExpr::Mul) {
        if (L->size() + R->size() - 2 > MaxPolynomialDegree)
          return std::nullopt;
        Polynomial Product(L->size() + R->size() - 1, CertInt(0));
        for (size_t I = 0; I != L->size(); ++I)
          for (size_t J = 0; J != R->size(); ++J)
            Product[I + J] = Product[I + J] + (*L)[I] * (*R)[J];
        Result = std::move(Product);
        break;
      }
      Polynomial Sum(std::max(L->size(), R->size()), CertInt(0));
      for (size_t I = 0; I != L->size(); ++I)
        Sum[I] = (*L)[I];
      for (size_t I = 0; I != R->size(); ++I)
        Sum[I] = E->K == LogicExpr::Add ? Sum[I] + (*R)[I] : Sum[I] - (*R)[I];
      Result = std::move(Sum);
      break;
    }
    default:
      return std::nullopt;
    }
    if (Result && E->Sort.Kind == LogicSortKind::BitVector)
      Fit.push_back({*Result, E->Sort});
    return Result;
  }

  static CertInt evaluate(const Polynomial &P, const CertInt &X) {
    CertInt Value(0);
    for (auto It = P.rbegin(); It != P.rend(); ++It)
      Value = Value * X + *It;
    return Value;
  }

  static CertInt magnitude(const CertInt &V) { return V.isNegative() ? -V : V; }

  /// Exact bounds of \p P over [Low, High], at least as wide as its range:
  /// expanded around the midpoint m, P(m + t) = d0 + d1 t + ..., so it lies
  /// within d0 -/+ sum |dk| h^k for |t| <= h.
  static std::pair<CertInt, CertInt>
  bounds(const Polynomial &P, const CertInt &Low, const CertInt &High) {
    const CertInt Mid = (Low + High).floorDiv(CertInt(2));
    const CertInt Half =
        std::max(Mid - Low, High - Mid,
                 [](const CertInt &L, const CertInt &R) { return L < R; });
    // Taylor shift by repeated synthetic division.
    Polynomial Shifted = P;
    for (size_t K = 0; K + 1 < Shifted.size(); ++K)
      for (size_t J = Shifted.size() - 1; J > K; --J)
        Shifted[J - 1] = Shifted[J - 1] + Mid * Shifted[J];
    CertInt Spread(0);
    CertInt Power(1);
    for (size_t K = 1; K < Shifted.size(); ++K) {
      Power = Power * Half;
      Spread = Spread + magnitude(Shifted[K]) * Power;
    }
    return {Shifted[0] - Spread, Shifted[0] + Spread};
  }

  /// The binder values in [Low, High] where the sign of \p P may differ from
  /// the value before it: every root, and the start of each run of one sign.
  /// False when that takes too long.
  static bool signChanges(const Polynomial &P, const CertInt &Low,
                          const CertInt &High, std::set<CertInt> &Values) {
    // Runs of one sign, in order: (start, sign), sign 0 for unknown points.
    std::vector<std::pair<CertInt, int>> Runs;
    std::vector<std::pair<CertInt, CertInt>> Work{{Low, High}};
    unsigned Steps = 0;
    while (!Work.empty()) {
      auto [A, B] = Work.back();
      Work.pop_back();
      if (++Steps > MaxIsolationSteps)
        return false;
      auto [Least, Most] = bounds(P, A, B);
      if (CertInt(0) < Least || Most < CertInt(0)) {
        Runs.push_back({A, CertInt(0) < Least ? 1 : -1});
        continue;
      }
      if (B - A < CertInt(8)) {
        for (CertInt X = A; !(B < X); X = X + CertInt(1)) {
          const CertInt Value = evaluate(P, X);
          Runs.push_back({X, Value.isZero() ? 0 : Value.isNegative() ? -1 : 1});
          Values.insert(X);
        }
        continue;
      }
      const CertInt Mid = (A + B).floorDiv(CertInt(2));
      // Left half last, so it is examined first.
      Work.push_back({Mid + CertInt(1), B});
      Work.push_back({A, Mid});
    }
    for (size_t I = 1; I < Runs.size(); ++I)
      if (Runs[I].second != Runs[I - 1].second)
        Values.insert(Runs[I].first);
    return true;
  }

  /// Whether \p P stays within \p Sort over [Low, High].
  static bool fitsOver(const Polynomial &P, const CertInt &Low,
                       const CertInt &High, const LogicSort &Sort) {
    const bool Signed = Sort.Signedness == LogicSignedness::Signed;
    const CertInt Min =
        Signed ? -CertInt::powerOfTwo(Sort.BitWidth - 1) : CertInt(0);
    const CertInt Max =
        CertInt::powerOfTwo(Signed ? Sort.BitWidth - 1 : Sort.BitWidth) -
        CertInt(1);
    std::vector<std::pair<CertInt, CertInt>> Work{{Low, High}};
    unsigned Steps = 0;
    while (!Work.empty()) {
      auto [A, B] = Work.back();
      Work.pop_back();
      if (++Steps > MaxIsolationSteps)
        return false;
      auto [Least, Most] = bounds(P, A, B);
      if (!(Least < Min) && !(Max < Most))
        continue;
      if (B - A < CertInt(8)) {
        for (CertInt X = A; !(B < X); X = X + CertInt(1)) {
          const CertInt Value = evaluate(P, X);
          if (Value < Min || Max < Value)
            return false;
        }
        continue;
      }
      const CertInt Mid = (A + B).floorDiv(CertInt(2));
      Work.push_back({Mid + CertInt(1), B});
      Work.push_back({A, Mid});
    }
    return true;
  }

  /// The exact value of a comparison operand at one binder value. A
  /// conversion to a machine sort is read before it reduces; \p Fits is
  /// cleared when that differs from the reduced value.
  std::optional<CertInt> comparedValue(const LogicExpr *E, bool &Fits) {
    if (E->K != LogicExpr::IntToBv)
      return integerOf(E);
    std::optional<CertInt> Exact = integerOf(E->Children[0].get());
    if (Exact && !(reduce(*Exact, E->Sort) == *Exact))
      Fits = false;
    return Exact;
  }

  /// The loads and collection reads, each at an address or key affine in the
  /// binder, and the comparisons between affine terms, through which alone
  /// \p E depends on the binder; false when it depends on the binder
  /// otherwise.
  static bool binderReads(const LogicExpr *E, const std::string &Binder,
                          std::vector<const LogicExpr *> &Loads,
                          std::vector<const LogicExpr *> &Comparisons) {
    if (!mentions(E, Binder))
      return true;
    switch (E->K) {
    case LogicExpr::Eq:
    case LogicExpr::Ne:
    case LogicExpr::Lt:
    case LogicExpr::Le:
    case LogicExpr::Gt:
    case LogicExpr::Ge:
      if (comparesPolynomial(E->Children[0].get(), Binder) &&
          comparesPolynomial(E->Children[1].get(), Binder)) {
        Comparisons.push_back(E);
        return true;
      }
      break;
    default:
      break;
    }
    if (E->K == LogicExpr::Select || isCollectionRead(*E)) {
      if (mentions(E->Children[0].get(), Binder) ||
          !affineIn(E->Children[1].get(), Binder))
        return false;
      Loads.push_back(E);
      return true;
    }
    if (E->K == LogicExpr::Var || E->K == LogicExpr::Forall ||
        E->K == LogicExpr::Exists || E->K == LogicExpr::SpecCall ||
        E->K == LogicExpr::Store || E->K == LogicExpr::HeapFrame)
      return false;
    return llvm::all_of(
        E->Children, [&](const std::unique_ptr<LogicExpr> &Child) {
          return binderReads(Child.get(), Binder, Loads, Comparisons);
        });
  }

  /// The binder values in [Low, High) at which some load of the body reads a
  /// cell its heap sets explicitly or some comparison may change. Between two
  /// of them every load reads its heap's default and every comparison keeps
  /// its truth, so the body has one value there. nullopt when the body depends
  /// on the binder in another way. Unbounded, the values anywhere, and every
  /// converted value must not depend on the binder: beyond the extreme values
  /// the body is then constant.
  std::optional<std::set<CertInt>> distinguishedValues(const LogicExpr *E,
                                                       const CertInt &Low,
                                                       const CertInt &High,
                                                       bool Unbounded = false) {
    std::vector<const LogicExpr *> Loads;
    std::vector<const LogicExpr *> Comparisons;
    if (!binderReads(E->Children.back().get(), E->Binder, Loads, Comparisons))
      return std::nullopt;
    auto inRange = [&](const CertInt &Value) {
      return Unbounded || (!(Value < Low) && Value < High);
    };
    std::set<CertInt> Values;
    for (const LogicExpr *Comparison : Comparisons) {
      if (!comparesAffine(Comparison->Children[0].get(), E->Binder) ||
          !comparesAffine(Comparison->Children[1].get(), E->Binder)) {
        // Between the sign changes of left - right, its truth is constant.
        std::vector<std::pair<Polynomial, LogicSort>> Fit;
        std::optional<Polynomial> Operands[2];
        for (unsigned Side : {0U, 1U}) {
          Operands[Side] =
              polynomialOf(Comparison->Children[Side].get(), E->Binder, Fit);
          if (!Operands[Side])
            return std::nullopt;
        }
        for (const auto &[Value, Sort] : Fit) {
          if (Unbounded &&
              llvm::any_of(llvm::drop_begin(Value),
                           [](const CertInt &C) { return !C.isZero(); }))
            return std::nullopt;
          if (!fitsOver(Value, Unbounded ? CertInt(0) : Low,
                        Unbounded ? CertInt(0) : High - CertInt(1), Sort))
            return std::nullopt;
        }
        Polynomial Difference(
            std::max(Operands[0]->size(), Operands[1]->size()), CertInt(0));
        for (size_t I = 0; I != Operands[0]->size(); ++I)
          Difference[I] = (*Operands[0])[I];
        for (size_t I = 0; I != Operands[1]->size(); ++I)
          Difference[I] = Difference[I] - (*Operands[1])[I];
        if (!Unbounded) {
          if (!signChanges(Difference, Low, High - CertInt(1), Values))
            return std::nullopt;
          continue;
        }
        // Every real root lies within 1 + max |a_i| / |a_n| of zero.
        CertInt Reach(2);
        for (const CertInt &Coefficient : Difference) {
          const CertInt Magnitude =
              Coefficient.isNegative() ? -Coefficient : Coefficient;
          if (Reach < Magnitude + CertInt(2))
            Reach = Magnitude + CertInt(2);
        }
        if (!signChanges(Difference, -Reach, Reach, Values))
          return std::nullopt;
        continue;
      }
      // A converted operand must not wrap anywhere in the range, which for
      // an affine term is decided at its ends. Over all integers, a far end
      // leaves every sort when the operand depends on the binder.
      bool Fits = true;
      const CertInt Far = CertInt::powerOfTwo(9000);
      for (const CertInt &End :
           {Unbounded ? -Far : Low, Unbounded ? Far : High - CertInt(1)}) {
        Scope.emplace_back(E->Binder, LogicValue::integer(End));
        std::optional<CertInt> Left =
            comparedValue(Comparison->Children[0].get(), Fits);
        std::optional<CertInt> Right =
            Left ? comparedValue(Comparison->Children[1].get(), Fits)
                 : std::nullopt;
        Scope.pop_back();
        if (!Right || !Fits)
          return std::nullopt;
      }
      CertInt Difference[2];
      for (int64_t I : {0, 1}) {
        Scope.emplace_back(E->Binder, LogicValue::integer(CertInt(I)));
        std::optional<CertInt> Left =
            comparedValue(Comparison->Children[0].get(), Fits);
        std::optional<CertInt> Right =
            Left ? comparedValue(Comparison->Children[1].get(), Fits)
                 : std::nullopt;
        Scope.pop_back();
        if (!Right)
          return std::nullopt;
        Difference[I] = *Left - *Right;
      }
      const CertInt Slope = Difference[1] - Difference[0];
      if (Slope.isZero())
        continue;
      // The sign changes where Difference[0] + Slope * i crosses zero.
      const CertInt Root = (-Difference[0]).floorDiv(Slope);
      for (int64_t Near = -1; Near <= 2; ++Near) {
        const CertInt Value = Root + CertInt(Near);
        if (inRange(Value))
          Values.insert(Value);
      }
    }
    for (const LogicExpr *Load : Loads) {
      std::shared_ptr<const HeapValue> Cells = readCells(*Load);
      if (!Cells)
        return std::nullopt;
      CertInt At[2];
      for (int64_t I : {0, 1}) {
        Scope.emplace_back(E->Binder, LogicValue::integer(CertInt(I)));
        std::optional<CertInt> Address = integerOf(Load->Children[1].get());
        Scope.pop_back();
        if (!Address)
          return std::nullopt;
        At[I] = *Address;
      }
      const CertInt Stride = At[1] - At[0];
      if (Stride.isZero())
        continue;
      // The body may change only where a load crosses a break: at the
      // binder values on either side of it.
      for (const auto &[Break, Unused] : Cells->Breaks) {
        (void)Unused;
        const CertInt Index = (Break - At[0]).floorDiv(Stride);
        for (const CertInt &Near : {Index, Index + CertInt(1)})
          if (inRange(Near))
            Values.insert(Near);
      }
    }
    return Values;
  }

  /// What a load or collection read reads, cell by cell: a heap; a sequence
  /// as 0 before index 0, its elements, then 0 from its length on; a set's
  /// membership, a multiset's counts, or a map's domain or values.
  std::shared_ptr<const HeapValue> readCells(const LogicExpr &Read) {
    std::optional<LogicValue> Value = eval(Read.Children[0].get());
    if (!Value)
      return nullptr;
    if (Read.K == LogicExpr::Select)
      return Value->K == LogicValue::Kind::Heap ? Value->Heap : nullptr;
    switch (Read.CollectionOp) {
    case LogicCollectionOp::SeqIndex: {
      if (Value->K != LogicValue::Kind::Seq)
        return nullptr;
      HeapValue Cells;
      const std::vector<CertInt> &Elements = *Value->Elements;
      for (size_t I = 0; I != Elements.size(); ++I)
        Cells.Breaks[CertInt(static_cast<int64_t>(I))] = Elements[I];
      Cells.Breaks[CertInt(static_cast<int64_t>(Elements.size()))] = CertInt(0);
      Cells.normalize();
      return std::make_shared<const HeapValue>(std::move(Cells));
    }
    case LogicCollectionOp::SetContains:
    case LogicCollectionOp::MultisetCount:
    case LogicCollectionOp::MapContains:
      return Value->Heap;
    case LogicCollectionOp::MapGet:
      return Value->K == LogicValue::Kind::Map ? Value->Values : nullptr;
    default:
      return nullptr;
    }
  }

  // Quantifiers as Presburger formulas. Once the model fixes everything but
  // the binders, a body built from comparisons of linear terms, reads at
  // linear addresses (each read is one of finitely many constant pieces of
  // its heap or collection), and nested quantifiers is a formula of linear
  // integer arithmetic, which Cooper's method decides exactly.

  /// Each piece holds where its guard does; the guards partition the
  /// integers.
  using Pieces =
      std::vector<std::pair<presburger::FormulaPtr, presburger::Linear>>;

  /// Binders being decided symbolically, innermost last, with the unique
  /// variable naming each.
  std::vector<std::pair<std::string, std::string>> Symbolic;
  /// Set when a term lies outside the decided fragment.
  bool OutsideFragment = false;

  static constexpr uint64_t MaxPresburgerNodes = 200000;
  static constexpr size_t MaxPieces = 4096;

  const std::string *symbolicName(const std::string &Name) const {
    for (auto It = Symbolic.rbegin(); It != Symbolic.rend(); ++It)
      if (It->first == Name)
        return &It->second;
    return nullptr;
  }

  bool mentionsSymbolic(const LogicExpr *E) const {
    if (E->K == LogicExpr::Var && symbolicName(E->Name))
      return true;
    return llvm::any_of(E->Children, [&](const std::unique_ptr<LogicExpr> &C) {
      return mentionsSymbolic(C.get());
    });
  }

  std::nullopt_t outside() {
    OutsideFragment = true;
    return std::nullopt;
  }

  std::optional<Pieces> constantPieces(const CertInt &Value) {
    return Pieces{
        {presburger::truth(true), presburger::Linear::constant(Value)}};
  }

  /// The pieces of an integer term.
  std::optional<Pieces> termOf(const LogicExpr *E) {
    using namespace presburger;
    if (!mentionsSymbolic(E)) {
      std::optional<CertInt> Value = integerOf(E);
      if (!Value)
        return std::nullopt;
      return constantPieces(*Value);
    }
    auto combine = [&](const Pieces &L, const Pieces &R,
                       auto Op) -> std::optional<Pieces> {
      Pieces Out;
      for (const auto &[LG, LT] : L)
        for (const auto &[RG, RT] : R) {
          std::optional<Linear> T = Op(LT, RT);
          if (!T)
            return outside();
          Out.push_back({conjunction({LG, RG}), std::move(*T)});
          if (Out.size() > MaxPieces)
            return outside();
        }
      return Out;
    };
    const bool Machine = E->Sort.Kind == LogicSortKind::BitVector;
    switch (E->K) {
    case LogicExpr::Var:
      return Pieces{{truth(true), Linear::variable(*symbolicName(E->Name))}};
    case LogicExpr::Neg: {
      std::optional<Pieces> Inner = termOf(E->Children[0].get());
      if (!Inner)
        return std::nullopt;
      for (auto &[G, T] : *Inner) {
        if (Machine) {
          if (!T.isConstant())
            return outside();
          T = Linear::constant(reduce(-T.Constant, E->Sort));
          continue;
        }
        T = T.scaled(CertInt(-1));
      }
      return Inner;
    }
    case LogicExpr::Add:
    case LogicExpr::Sub:
    case LogicExpr::Mul:
    case LogicExpr::Div:
    case LogicExpr::Rem: {
      std::optional<Pieces> L = termOf(E->Children[0].get());
      if (!L)
        return std::nullopt;
      std::optional<Pieces> R = termOf(E->Children[1].get());
      if (!R)
        return std::nullopt;
      return combine(
          *L, *R,
          [&](const Linear &A, const Linear &B) -> std::optional<Linear> {
            if (A.isConstant() && B.isConstant()) {
              std::optional<LogicValue> V =
                  Machine ? machineArithmetic(E, A.Constant, B.Constant)
                          : constantArithmetic(E->K, A.Constant, B.Constant);
              if (!V || V->K != LogicValue::Kind::Integer)
                return std::nullopt;
              return Linear::constant(V->Integer);
            }
            // Machine operations may wrap; division is not
            // linear.
            if (Machine || E->K == LogicExpr::Div || E->K == LogicExpr::Rem)
              return std::nullopt;
            if (E->K == LogicExpr::Add)
              return A + B;
            if (E->K == LogicExpr::Sub)
              return A - B;
            if (A.isConstant())
              return B.scaled(A.Constant);
            if (B.isConstant())
              return A.scaled(B.Constant);
            return std::nullopt;
          });
    }
    case LogicExpr::Ite: {
      FormulaPtr Condition = formulaOf(E->Children[0].get());
      if (!Condition)
        return std::nullopt;
      std::optional<Pieces> Then = termOf(E->Children[1].get());
      if (!Then)
        return std::nullopt;
      std::optional<Pieces> Else = termOf(E->Children[2].get());
      if (!Else)
        return std::nullopt;
      Pieces Out;
      for (auto &[G, T] : *Then)
        Out.push_back({conjunction({Condition, G}), T});
      for (auto &[G, T] : *Else)
        Out.push_back({conjunction({negation(Condition), G}), T});
      return Out;
    }
    case LogicExpr::BvToInt:
      return termOf(E->Children[0].get());
    case LogicExpr::IntToBv:
    case LogicExpr::BvResize: {
      std::optional<Pieces> Inner = termOf(E->Children[0].get());
      if (!Inner)
        return std::nullopt;
      for (auto &[G, T] : *Inner) {
        if (!T.isConstant())
          return outside();
        T = Linear::constant(
            E->K == LogicExpr::IntToBv
                ? reduce(T.Constant, E->Sort)
                : convertMachine(T.Constant, E->Children[0]->Sort, E->Sort));
      }
      return Inner;
    }
    case LogicExpr::Select:
    case LogicExpr::Collection: {
      if (E->K == LogicExpr::Collection &&
          E->CollectionOp != LogicCollectionOp::SeqIndex &&
          E->CollectionOp != LogicCollectionOp::MultisetCount &&
          E->CollectionOp != LogicCollectionOp::MapGet)
        return outside();
      return readPieces(*E);
    }
    default:
      return outside();
    }
  }

  std::optional<LogicValue>
  constantArithmetic(LogicExpr::Kind K, const CertInt &L, const CertInt &R) {
    switch (K) {
    case LogicExpr::Add:
      return integer(L + R);
    case LogicExpr::Sub:
      return integer(L - R);
    case LogicExpr::Mul:
      return integer(L * R);
    case LogicExpr::Div:
      return integer(R.isZero() ? CertInt() : L.truncDiv(R));
    case LogicExpr::Rem:
      return integer(R.isZero() ? L : L - R * L.truncDiv(R));
    default:
      return std::nullopt;
    }
  }

  /// The pieces of a read at a symbolic address or key: the value of each
  /// run of its cells, where the address falls in that run.
  std::optional<Pieces> readPieces(const LogicExpr &Read) {
    using namespace presburger;
    if (mentionsSymbolic(Read.Children[0].get()))
      return outside();
    std::optional<Pieces> Keys = termOf(Read.Children[1].get());
    if (!Keys)
      return std::nullopt;
    std::shared_ptr<const HeapValue> Cells = readCells(Read);
    if (!Cells)
      return Failure.empty() ? outside() : std::nullopt;
    Pieces Out;
    for (const auto &[G, Key] : *Keys) {
      std::optional<CertInt> Start;
      CertInt Value = Cells->Default;
      auto run = [&](const std::optional<CertInt> &From,
                     const std::optional<CertInt> &To, const CertInt &V) {
        std::vector<FormulaPtr> Guard{G};
        if (From)
          Guard.push_back(lessEqual(Linear::constant(*From), Key));
        if (To)
          Guard.push_back(less(Key, Linear::constant(*To)));
        Out.push_back({conjunction(std::move(Guard)), Linear::constant(V)});
      };
      for (const auto &[Break, Cell] : Cells->Breaks) {
        run(Start, Break, Value);
        Start = Break;
        Value = Cell;
      }
      run(Start, std::nullopt, Value);
      if (Out.size() > MaxPieces)
        return outside();
    }
    return Out;
  }

  /// The formula of a Boolean term.
  presburger::FormulaPtr formulaOf(const LogicExpr *E) {
    using namespace presburger;
    if (!mentionsSymbolic(E) && E->K != LogicExpr::Forall &&
        E->K != LogicExpr::Exists) {
      std::optional<bool> Holds = truthOf(E);
      return Holds ? truth(*Holds) : nullptr;
    }
    auto children = [&](std::vector<FormulaPtr> &Out) {
      for (const auto &Child : E->Children) {
        FormulaPtr F = formulaOf(Child.get());
        if (!F)
          return false;
        Out.push_back(std::move(F));
      }
      return true;
    };
    switch (E->K) {
    case LogicExpr::True:
      return truth(true);
    case LogicExpr::False:
      return truth(false);
    case LogicExpr::Not: {
      FormulaPtr Inner = formulaOf(E->Children[0].get());
      return Inner ? negation(Inner) : nullptr;
    }
    case LogicExpr::And:
    case LogicExpr::Or: {
      std::vector<FormulaPtr> Children;
      if (!children(Children))
        return nullptr;
      return E->K == LogicExpr::And ? conjunction(std::move(Children))
                                    : disjunction(std::move(Children));
    }
    case LogicExpr::Ite: {
      std::vector<FormulaPtr> Parts;
      if (!children(Parts))
        return nullptr;
      return disjunction({conjunction({Parts[0], Parts[1]}),
                          conjunction({negation(Parts[0]), Parts[2]})});
    }
    case LogicExpr::Eq:
    case LogicExpr::Ne:
    case LogicExpr::Lt:
    case LogicExpr::Le:
    case LogicExpr::Gt:
    case LogicExpr::Ge: {
      if (E->Children[0]->Sort.Kind == LogicSortKind::Bool) {
        std::vector<FormulaPtr> Sides;
        if (!children(Sides))
          return nullptr;
        FormulaPtr Same = disjunction(
            {conjunction({Sides[0], Sides[1]}),
             conjunction({negation(Sides[0]), negation(Sides[1])})});
        return E->K == LogicExpr::Ne ? negation(Same) : Same;
      }
      if (!isInteger(E->Children[0]->Sort) &&
          E->Children[0]->Sort.Kind != LogicSortKind::BitVector) {
        OutsideFragment = true;
        return nullptr;
      }
      std::optional<Pieces> L = termOf(E->Children[0].get());
      if (!L)
        return nullptr;
      std::optional<Pieces> R = termOf(E->Children[1].get());
      if (!R)
        return nullptr;
      std::vector<FormulaPtr> Cases;
      for (const auto &[LG, LT] : *L)
        for (const auto &[RG, RT] : *R) {
          FormulaPtr Atom;
          switch (E->K) {
          case LogicExpr::Eq:
          case LogicExpr::Ne:
            Atom = equal(LT, RT);
            break;
          case LogicExpr::Lt:
            Atom = less(LT, RT);
            break;
          case LogicExpr::Le:
            Atom = lessEqual(LT, RT);
            break;
          case LogicExpr::Gt:
            Atom = less(RT, LT);
            break;
          default:
            Atom = lessEqual(RT, LT);
            break;
          }
          Cases.push_back(conjunction({LG, RG, Atom}));
        }
      FormulaPtr Holds = disjunction(std::move(Cases));
      return E->K == LogicExpr::Ne ? negation(Holds) : Holds;
    }
    case LogicExpr::Collection: {
      if (E->CollectionOp != LogicCollectionOp::SetContains &&
          E->CollectionOp != LogicCollectionOp::MapContains) {
        OutsideFragment = true;
        return nullptr;
      }
      std::optional<Pieces> Members = readPieces(*E);
      if (!Members)
        return nullptr;
      std::vector<FormulaPtr> Cases;
      for (const auto &[G, T] : *Members)
        if (!T.Constant.isZero())
          Cases.push_back(G);
      return disjunction(std::move(Cases));
    }
    case LogicExpr::Forall:
    case LogicExpr::Exists: {
      const bool Forall = E->K == LogicExpr::Forall;
      const std::string Variable =
          E->Binder + "#" + std::to_string(Symbolic.size());
      std::vector<FormulaPtr> Range;
      if (E->Children.size() == 3) {
        std::optional<Pieces> Low = termOf(E->Children[0].get());
        if (!Low)
          return nullptr;
        std::optional<Pieces> High = termOf(E->Children[1].get());
        if (!High)
          return nullptr;
        const Linear V = Linear::variable(Variable);
        std::vector<FormulaPtr> Above, Below;
        for (const auto &[G, T] : *Low)
          Above.push_back(conjunction({G, lessEqual(T, V)}));
        for (const auto &[G, T] : *High)
          Below.push_back(conjunction({G, less(V, T)}));
        Range.push_back(disjunction(std::move(Above)));
        Range.push_back(disjunction(std::move(Below)));
      }
      Symbolic.emplace_back(E->Binder, Variable);
      FormulaPtr Body = formulaOf(E->Children.back().get());
      Symbolic.pop_back();
      if (!Body)
        return nullptr;
      FormulaPtr InRange = conjunction(std::move(Range));
      if (Forall)
        return forall(Variable, disjunction({negation(InRange), Body}));
      return exists(Variable, conjunction({InRange, Body}));
    }
    default:
      OutsideFragment = true;
      return nullptr;
    }
  }

  /// The truth of quantifier E by Presburger arithmetic; nullopt with
  /// OutsideFragment set when E is outside it, or with Failure set.
  std::optional<bool> presburgerTruth(const LogicExpr *E) {
    OutsideFragment = false;
    Steps += countTerms(E);
    const size_t SavedSymbolic = Symbolic.size();
    presburger::FormulaPtr F = formulaOf(E);
    Symbolic.resize(SavedSymbolic);
    if (!F)
      return std::nullopt;
    std::optional<bool> Holds = presburger::decide(F, MaxPresburgerNodes);
    if (!Holds)
      OutsideFragment = true;
    return Holds;
  }

  /// The binder values around which a comparison of \p E's body, affine in
  /// the binder once applications at it are unfolded, changes.
  std::set<CertInt> candidateWitnesses(const LogicExpr *E) {
    std::vector<std::unique_ptr<LogicExpr>> Unfolded;
    std::vector<const LogicExpr *> Comparisons;
    std::function<void(const LogicExpr *)> collect = [&](const LogicExpr *C) {
      switch (C->K) {
      case LogicExpr::Eq:
      case LogicExpr::Ne:
      case LogicExpr::Lt:
      case LogicExpr::Le:
      case LogicExpr::Gt:
      case LogicExpr::Ge:
        if (mentions(C, E->Binder) &&
            comparesAffine(C->Children[0].get(), E->Binder) &&
            comparesAffine(C->Children[1].get(), E->Binder))
          Comparisons.push_back(C);
        break;
      default:
        break;
      }
      for (const auto &Child : C->Children)
        collect(Child.get());
    };
    for (unsigned Recursive = 0; Recursive != 3; ++Recursive) {
      Unfolded.push_back(cloneLogicExpr(E->Children.back().get()));
      uint64_t Budget = MaxUnfoldedTerms;
      inlineAt(Unfolded.back(), E->Binder, 4, Recursive, Budget);
      Steps += MaxUnfoldedTerms - Budget;
      collect(Unfolded.back().get());
    }
    std::set<CertInt> Values;
    for (const LogicExpr *Comparison : Comparisons) {
      if (Values.size() >= Limits.QuantifierProbe)
        break;
      const bool SavedLimit = LimitInDefinition;
      CertInt Difference[2];
      bool Known = true;
      for (int64_t I : {0, 1}) {
        bool Fits = true;
        Scope.emplace_back(E->Binder, LogicValue::integer(CertInt(I)));
        std::optional<CertInt> Left =
            comparedValue(Comparison->Children[0].get(), Fits);
        std::optional<CertInt> Right =
            Left ? comparedValue(Comparison->Children[1].get(), Fits)
                 : std::nullopt;
        Scope.pop_back();
        if (!Right) {
          Known = false;
          break;
        }
        Difference[I] = *Left - *Right;
      }
      if (!Known) {
        if (spent())
          break;
        Failure.clear();
        LimitInDefinition = SavedLimit;
        continue;
      }
      const CertInt Slope = Difference[1] - Difference[0];
      if (Slope.isZero())
        continue;
      const CertInt Root = (-Difference[0]).floorDiv(Slope);
      for (int64_t Near = -1; Near <= 2; ++Near)
        Values.insert(Root + CertInt(Near));
    }
    return Values;
  }

  /// Over all integers: the distinguished values, one value between each
  /// two, and one beyond each end, where the body is constant.
  std::optional<LogicValue> unboundedQuantifier(const LogicExpr *E) {
    const bool Forall = E->K == LogicExpr::Forall;
    std::optional<std::set<CertInt>> Distinguished =
        distinguishedValues(E, CertInt(0), CertInt(0), /*Unbounded=*/true);
    if (!Distinguished) {
      if (!Failure.empty())
        return std::nullopt;
      if (std::optional<bool> Holds = presburgerTruth(E))
        return LogicValue::boolean(*Holds);
      if (!Failure.empty())
        return std::nullopt;
      if (std::optional<LogicValue> Decided =
              byWitnesses(E, CertInt(0), CertInt(0), /*Bounded=*/false))
        return Decided;
      if (!Failure.empty())
        return std::nullopt;
      // A witness still decides it: a value where the body holds proves an
      // exists, one where it fails refutes a forall (an inductive
      // predicate's derivation height, for one). The values where the
      // body's comparisons change, once its non-recursive applications are
      // unfolded, come first, then values near zero.
      std::set<CertInt> Candidates = candidateWitnesses(E);
      std::vector<CertInt> Binders(Candidates.begin(), Candidates.end());
      for (unsigned I = 0; I != Limits.QuantifierProbe; ++I)
        for (const CertInt &Binder : {CertInt(static_cast<int64_t>(I)),
                                      CertInt(-static_cast<int64_t>(I) - 1)})
          if (!Candidates.count(Binder))
            Binders.push_back(Binder);
      std::optional<bool> Decided =
          decidingInstance(E->Children[0].get(), E->Binder, Binders, Forall);
      if (!Decided)
        return std::nullopt;
      if (*Decided)
        return LogicValue::boolean(!Forall);
      return limit("an unbounded quantifier whose body depends on its binder "
                   "other than through linear arithmetic, reads, and "
                   "quantifiers, with no witness among the values tried");
    }
    std::set<CertInt> Checked = *Distinguished;
    if (Distinguished->empty()) {
      Checked.insert(CertInt(0));
    } else {
      Checked.insert(*Distinguished->begin() - CertInt(1));
      Checked.insert(*Distinguished->rbegin() + CertInt(1));
      const CertInt *Previous = nullptr;
      for (const CertInt &Value : *Distinguished) {
        if (Previous && *Previous + CertInt(1) < Value)
          Checked.insert(*Previous + CertInt(1));
        Previous = &Value;
      }
    }
    return overBinders(E->Children[0].get(), E->Binder,
                       std::vector<CertInt>(Checked.begin(), Checked.end()),
                       Forall);
  }

  std::optional<LogicValue> quantifier(const LogicExpr *E) {
    if (!Fixpoints.empty() &&
        appliesAny(E->Children.back().get(), Fixpoints.back()->Group))
      return fixpointQuantifier(E);
    if (E->Children.size() == 1)
      return unboundedQuantifier(E);
    std::optional<CertInt> Low = integerOf(E->Children[0].get());
    if (!Low)
      return std::nullopt;
    std::optional<CertInt> High = integerOf(E->Children[1].get());
    if (!High)
      return std::nullopt;
    const bool Forall = E->K == LogicExpr::Forall;
    if (!(*Low < *High))
      return LogicValue::boolean(Forall);
    const CertInt Count = *High - *Low;
    const LogicExpr *Body = E->Children[2].get();
    // A body that depends on the binder only through loads has one value
    // wherever they all read default cells: check the other values and one
    // representative.
    if (CertInt(static_cast<int64_t>(Limits.DirectExpansion)) < Count) {
      if (std::optional<std::set<CertInt>> Distinguished =
              distinguishedValues(E, *Low, *High)) {
        // Each distinguished value, and one value in each gap between them.
        std::set<CertInt> Checked = *Distinguished;
        CertInt Gap = *Low;
        for (const CertInt &Binder : *Distinguished) {
          if (Gap < Binder)
            Checked.insert(Gap);
          Gap = Binder + CertInt(1);
        }
        if (Gap < *High)
          Checked.insert(Gap);
        return overBinders(Body, E->Binder,
                           std::vector<CertInt>(Checked.begin(), Checked.end()),
                           Forall);
      }
      if (!Failure.empty())
        return std::nullopt;
      if (std::optional<bool> Holds = presburgerTruth(E))
        return LogicValue::boolean(*Holds);
      if (!Failure.empty())
        return std::nullopt;
      if (std::optional<LogicValue> Decided =
              byWitnesses(E, *Low, *High, /*Bounded=*/true))
        return Decided;
      if (!Failure.empty())
        return std::nullopt;
    }
    const uint64_t Remaining = Limits.QuantifierInstances -
                               std::min(Instances, Limits.QuantifierInstances);
    if (CertInt(static_cast<int64_t>(
            std::min<uint64_t>(Remaining, INT64_MAX))) < Count) {
      // One instance still decides a range too wide to expand.
      const bool Closed = Scope.empty() && Active.empty();
      std::vector<CertInt> Ends;
      for (unsigned I = 0; I != Limits.QuantifierProbe; ++I) {
        Ends.push_back(*Low + CertInt(I));
        Ends.push_back(*High - CertInt(1) - CertInt(I));
      }
      std::optional<bool> Decided =
          decidingInstance(Body, E->Binder, Ends, Forall);
      if (!Decided)
        return std::nullopt;
      if (*Decided)
        return LogicValue::boolean(!Forall);
      if (Closed)
        Wide = E;
      return limit("a quantifier range of " + Count.toDecimal() +
                   " values is too wide to expand");
    }
    std::optional<bool> Decided = decidingInstance(
        Body, E->Binder, static_cast<size_t>(Count.bits(64).getZExtValue()),
        [&](size_t I) { return *Low + CertInt(static_cast<int64_t>(I)); },
        Forall);
    if (!Decided)
      return std::nullopt;
    return LogicValue::boolean(*Decided ? !Forall : Forall);
  }

  const LogicFunctionDecl *function(const std::string &Identity) const {
    if (auto It = Module.LogicFunctions.find(Identity);
        It != Module.LogicFunctions.end())
      return &It->second;
    if (auto It = Module.EvidenceFunctions.find(Identity);
        It != Module.EvidenceFunctions.end())
      return &It->second;
    return nullptr;
  }

  static void appliedFunctions(const LogicExpr *E, std::set<std::string> &Out) {
    if (!E)
      return;
    if (E->K == LogicExpr::SpecCall)
      Out.insert(E->SpecCallee);
    for (const auto &Child : E->Children)
      appliedFunctions(Child.get(), Out);
  }

  /// The inductive predicates defined with \p Predicate: those its unfolding
  /// reaches that reach it back.
  std::set<std::string> groupOf(const LogicFunctionDecl &Predicate) {
    std::map<std::string, std::set<std::string>> Applies;
    auto successors = [&](const std::string &Identity) {
      auto [It, Inserted] = Applies.try_emplace(Identity);
      if (Inserted)
        if (const LogicFunctionDecl *Function = function(Identity);
            Function && Function->Unfolding) {
          std::set<std::string> Called;
          appliedFunctions(Function->Unfolding.get(), Called);
          for (const std::string &Callee : Called)
            if (const LogicFunctionDecl *Other = function(Callee);
                Other && Other->Unfolding)
              It->second.insert(Callee);
        }
      return It->second;
    };
    auto reaches = [&](const std::string &From, const std::string &To) {
      std::set<std::string> Seen{From};
      std::vector<std::string> Work{From};
      while (!Work.empty()) {
        const std::string Current = Work.back();
        Work.pop_back();
        for (const std::string &Next : successors(Current)) {
          if (Next == To)
            return true;
          if (Seen.insert(Next).second)
            Work.push_back(Next);
        }
      }
      return false;
    };
    std::set<std::string> Group{Predicate.Identity};
    std::set<std::string> Seen{Predicate.Identity};
    std::vector<std::string> Work{Predicate.Identity};
    while (!Work.empty()) {
      const std::string Current = Work.back();
      Work.pop_back();
      for (const std::string &Next : successors(Current))
        if (Seen.insert(Next).second) {
          Work.push_back(Next);
          if (reaches(Next, Predicate.Identity))
            Group.insert(Next);
        }
    }
    return Group;
  }

  size_t fixpointNode(Fixpoint &F, const LogicFunctionDecl &Function,
                      const std::vector<LogicValue> &Args) {
    std::string Key = Function.Identity;
    for (const LogicValue &Argument : Args)
      Key += "\x1f" + Argument.key();
    auto [It, Inserted] = F.Index.try_emplace(Key, F.Nodes.size());
    if (Inserted) {
      F.Nodes.push_back({&Function, Args});
      F.Values.push_back(false);
      F.Readers.emplace_back();
      F.Reads.emplace_back();
      F.Pending.push_back(It->second);
    }
    return It->second;
  }

  std::optional<bool> unfoldingAt(const LogicFunctionDecl &Function,
                                  const std::vector<LogicValue> &Args) {
    const size_t SavedBase = ScopeBase;
    const size_t SavedSize = Scope.size();
    ScopeBase = SavedSize;
    for (unsigned I = 0; I != Args.size(); ++I)
      Scope.emplace_back(Function.Parameters[I].Name, Args[I]);
    Active.push_back(&Function);
    std::optional<bool> Holds = truthOf(Function.Unfolding.get());
    Active.pop_back();
    Scope.resize(SavedSize);
    ScopeBase = SavedBase;
    return Holds;
  }

  /// An inductive predicate at \p Args by the least fixpoint of its group's
  /// unfoldings, explored breadth first from \p Args: true as soon as a
  /// derivation reaches it, since every value set true is derived; false
  /// once every argument its derivations reach is evaluated. nullopt, with
  /// the evaluation state as before, when they reach too many. \p Graph
  /// receives the explored nodes, node 0 being \p Args.
  std::optional<bool>
  leastFixpoint(const LogicFunctionDecl &Predicate,
                const std::vector<LogicValue> &Args,
                std::shared_ptr<const FixpointGraph> &Graph) {
    Fixpoint F;
    F.Group = groupOf(Predicate);
    for (const std::string &Member : F.Group)
      if (const LogicFunctionDecl *Function = function(Member);
          !Function || !Function->Unfolding)
        return std::nullopt;
    const bool SavedLimit = LimitInDefinition;
    const LogicExpr *SavedWide = Wide;
    const LogicExpr *SavedDeep = Deep;
    fixpointNode(F, Predicate, Args);
    Fixpoints.push_back(&F);
    bool Complete = true;
    while (!F.Pending.empty() && !F.Values[0]) {
      const size_t Node = F.Pending.front();
      F.Pending.pop_front();
      if (F.Values[Node])
        continue;
      if (F.Nodes.size() > MaxFixpointArguments) {
        Complete = false;
        break;
      }
      const LogicFunctionDecl *Function = F.Nodes[Node].first;
      const std::vector<LogicValue> NodeArgs = F.Nodes[Node].second;
      F.Reader = Node;
      std::optional<bool> Holds = unfoldingAt(*Function, NodeArgs);
      if (!Holds) {
        Complete = false;
        break;
      }
      if (*Holds) {
        F.Values[Node] = true;
        for (size_t Reader : F.Readers[Node])
          if (!F.Values[Reader])
            F.Pending.push_back(Reader);
      }
    }
    Fixpoints.pop_back();
    if (!F.Values[0] && !Complete) {
      if (spent())
        return std::nullopt;
      Failure.clear();
      LimitInDefinition = SavedLimit;
      Wide = SavedWide;
      Deep = SavedDeep;
      return std::nullopt;
    }
    if (F.Values[0] && !Failure.empty() && !spent()) {
      Failure.clear();
      LimitInDefinition = SavedLimit;
      Wide = SavedWide;
      Deep = SavedDeep;
    }
    auto Shared = std::make_shared<FixpointGraph>();
    Shared->Nodes = std::move(F.Nodes);
    Shared->Values = std::move(F.Values);
    Shared->Reads = std::move(F.Reads);
    Graph = Shared;
    // A value set true is exact; once exploration ended, every value is.
    const bool AllExact = F.Pending.empty() && Complete;
    for (const auto &[Key, Node] : F.Index)
      if (AllExact || Shared->Values[Node])
        Applications.emplace(Key,
                             Computed{LogicValue::boolean(Shared->Values[Node]),
                                      Shared, Node, false});
    return Shared->Values[0];
  }

  /// The unfoldings that decide a fixpoint's value at \p Node: for a true
  /// value, those of the derivation, through the true nodes it read; for a
  /// false one, those of every node it reaches.
  static std::vector<DefinitionInstance> derivation(const FixpointGraph &Graph,
                                                    size_t Node) {
    std::vector<DefinitionInstance> Out;
    const bool True = Graph.Values[Node];
    std::set<size_t> Seen{Node};
    std::vector<size_t> Work{Node};
    while (!Work.empty()) {
      const size_t Current = Work.back();
      Work.pop_back();
      Out.push_back({Graph.Nodes[Current].first, Graph.Nodes[Current].second,
                     DefinitionInstance::Kind::Unfolding});
      for (size_t Next : Graph.Reads[Current])
        if ((!True || Graph.Values[Next]) && Seen.insert(Next).second)
          Work.push_back(Next);
    }
    return Out;
  }

  static std::vector<DefinitionInstance>
  justification(const Computed &Value, const LogicFunctionDecl &Function,
                const std::vector<LogicValue> &Args) {
    if (Value.Graph)
      return derivation(*Value.Graph, Value.Node);
    if (Value.ByPostcondition)
      return {{&Function, Args, DefinitionInstance::Kind::Postcondition}};
    return {};
  }

  static std::unique_ptr<LogicExpr> trueTerm() {
    auto True = std::make_unique<LogicExpr>(LogicExpr::True);
    True->Sort = LogicSort::boolSort();
    return True;
  }

  /// The names \p E mentions, as variables or binders.
  static void namesIn(const LogicExpr *E, std::set<std::string> &Out) {
    if (E->K == LogicExpr::Var)
      Out.insert(E->Name);
    if (E->K == LogicExpr::Forall || E->K == LogicExpr::Exists)
      Out.insert(E->Binder);
    for (const auto &Child : E->Children)
      namesIn(Child.get(), Out);
  }

  /// Renames the occurrences of \p From in \p E that are not bound below
  /// it to \p To.
  static void rename(LogicExpr *E, const std::string &From,
                     const std::string &To) {
    if (E->K == LogicExpr::Var && E->Name == From) {
      E->Name = To;
      return;
    }
    const bool Binds =
        (E->K == LogicExpr::Forall || E->K == LogicExpr::Exists) &&
        E->Binder == From;
    for (size_t I = 0; I != E->Children.size(); ++I)
      if (!Binds || I + 1 != E->Children.size())
        rename(E->Children[I].get(), From, To);
    if (!Binds)
      for (auto &Pattern : E->Patterns)
        rename(Pattern.get(), From, To);
  }

  /// Substitutes \p Map in \p E. A binder that a substituted value mentions
  /// is renamed apart first, since the value would be captured otherwise.
  static void substitute(std::unique_ptr<LogicExpr> &E,
                         const std::map<std::string, const LogicExpr *> &Map) {
    if (E->K == LogicExpr::Var)
      if (auto It = Map.find(E->Name); It != Map.end()) {
        E = cloneLogicExpr(It->second);
        return;
      }
    if (E->K != LogicExpr::Forall && E->K != LogicExpr::Exists) {
      for (auto &Child : E->Children)
        substitute(Child, Map);
      return;
    }
    for (size_t I = 0; I + 1 < E->Children.size(); ++I)
      substitute(E->Children[I], Map);
    std::map<std::string, const LogicExpr *> Inner = Map;
    Inner.erase(E->Binder);
    std::set<std::string> Taken;
    for (const auto &[Name, Value] : Inner)
      namesIn(Value, Taken);
    if (Taken.count(E->Binder)) {
      namesIn(E->Children.back().get(), Taken);
      std::string Binder = E->Binder;
      for (unsigned N = 1; Taken.count(Binder); ++N)
        Binder = E->Binder + "." + std::to_string(N);
      rename(E->Children.back().get(), E->Binder, Binder);
      for (auto &Pattern : E->Patterns)
        rename(Pattern.get(), E->Binder, Binder);
      E->Binder = Binder;
    }
    substitute(E->Children.back(), Inner);
  }

  static std::unique_ptr<LogicExpr> falseTerm() {
    auto False = std::make_unique<LogicExpr>(LogicExpr::False);
    False->Sort = LogicSort::boolSort();
    return False;
  }

  /// Whether \p E applies a function at arguments that mention \p Binder.
  static bool appliesAt(const LogicExpr *E, const std::string &Binder) {
    if (E->K == LogicExpr::SpecCall && mentions(E, Binder))
      return true;
    return llvm::any_of(E->Children, [&](const std::unique_ptr<LogicExpr> &C) {
      return appliesAt(C.get(), Binder);
    });
  }

  /// Unfolds each application whose arguments mention \p Binder by its
  /// definition, an equation: \p Depth levels deep, of which \p Recursive
  /// may unfold recursive functions, while the term stays within \p Budget
  /// nodes.
  void inlineAt(std::unique_ptr<LogicExpr> &E, const std::string &Binder,
                unsigned Depth, unsigned Recursive, uint64_t &Budget) {
    if (E->K == LogicExpr::SpecCall && Depth && mentions(E.get(), Binder))
      if (const LogicFunctionDecl *Function = function(E->SpecCallee);
          Function && Function->StepDefinition && !Function->Choice &&
          Function->Parameters.size() == E->Children.size() &&
          (Recursive || nonRecursive().count(Function->Identity)) &&
          countTerms(Function->StepDefinition.get()) < Budget) {
        Budget -= countTerms(Function->StepDefinition.get());
        if (!nonRecursive().count(Function->Identity))
          --Recursive;
        std::unique_ptr<LogicExpr> Body =
            cloneLogicExpr(Function->StepDefinition.get());
        std::map<std::string, const LogicExpr *> Map;
        for (size_t I = 0; I != E->Children.size(); ++I)
          Map[Function->Parameters[I].Name] = E->Children[I].get();
        substitute(Body, Map);
        E = std::move(Body);
        inlineAt(E, Binder, Depth - 1, Recursive, Budget);
        return;
      }
    for (auto &Child : E->Children)
      inlineAt(Child, Binder, Depth, Recursive, Budget);
  }

  const std::set<std::string> &nonRecursive() {
    if (!NonRecursive)
      NonRecursive = nonRecursiveDefinitions(Module);
    return *NonRecursive;
  }

  static uint64_t countTerms(const LogicExpr *E) {
    uint64_t Count = 1;
    for (const auto &Child : E->Children)
      Count += countTerms(Child.get());
    return Count;
  }

  /// Replaces each condition that applies a function at \p Binder by true
  /// where \p E is monotone in it (\p Positive) and false where antitone,
  /// so that E implies the result. False when one occurs where E is
  /// neither.
  static bool approximate(std::unique_ptr<LogicExpr> &E, bool Positive,
                          const std::string &Binder) {
    if (!appliesAt(E.get(), Binder))
      return true;
    switch (E->K) {
    case LogicExpr::SpecCall:
      if (E->Sort.Kind != LogicSortKind::Bool)
        return false;
      E = Positive ? trueTerm() : falseTerm();
      return true;
    case LogicExpr::Not:
      return approximate(E->Children[0], !Positive, Binder);
    case LogicExpr::And:
    case LogicExpr::Or:
      return llvm::all_of(E->Children, [&](std::unique_ptr<LogicExpr> &C) {
        return approximate(C, Positive, Binder);
      });
    case LogicExpr::Ite:
      return E->Sort.Kind == LogicSortKind::Bool &&
             !appliesAt(E->Children[0].get(), Binder) &&
             approximate(E->Children[1], Positive, Binder) &&
             approximate(E->Children[2], Positive, Binder);
    case LogicExpr::Forall:
    case LogicExpr::Exists:
      // A condition in a monotone position may become true, in an antitone
      // one false: a quantifier over the binder is one the analysis below
      // cannot read.
      E = Positive ? trueTerm() : falseTerm();
      return true;
    default:
      return false;
    }
  }

  /// Replaces each condition of \p E that does not mention \p Binder by its
  /// value, and simplifies the connectives over them.
  void fold(std::unique_ptr<LogicExpr> &E, const std::string &Binder) {
    if (E->Sort.Kind != LogicSortKind::Bool)
      return;
    if (!mentions(E.get(), Binder)) {
      if (E->K == LogicExpr::True || E->K == LogicExpr::False)
        return;
      const bool SavedLimit = LimitInDefinition;
      std::optional<bool> Holds = truthOf(E.get());
      if (!Holds) {
        if (!spent()) {
          Failure.clear();
          LimitInDefinition = SavedLimit;
        }
        return;
      }
      E = *Holds ? trueTerm() : falseTerm();
      return;
    }
    switch (E->K) {
    case LogicExpr::Not:
      fold(E->Children[0], Binder);
      if (E->Children[0]->K == LogicExpr::True)
        E = falseTerm();
      else if (E->Children[0]->K == LogicExpr::False)
        E = trueTerm();
      return;
    case LogicExpr::And:
    case LogicExpr::Or: {
      const bool And = E->K == LogicExpr::And;
      for (auto &Child : E->Children) {
        fold(Child, Binder);
        if (Child->K == (And ? LogicExpr::False : LogicExpr::True)) {
          E = And ? falseTerm() : trueTerm();
          return;
        }
      }
      return;
    }
    case LogicExpr::Ite:
      fold(E->Children[0], Binder);
      fold(E->Children[1], Binder);
      fold(E->Children[2], Binder);
      if (E->Children[0]->K == LogicExpr::True) {
        std::unique_ptr<LogicExpr> Then = std::move(E->Children[1]);
        E = std::move(Then);
      } else if (E->Children[0]->K == LogicExpr::False) {
        std::unique_ptr<LogicExpr> Else = std::move(E->Children[2]);
        E = std::move(Else);
      }
      return;
    default:
      return;
    }
  }

  /// The binder values of quantifier \p Q at which its body may hold
  /// (\p Negated: may fail), when they are finitely many: found where the
  /// comparisons of the body change, once its applications at the binder
  /// are unfolded or approximated. nullopt when they are not, or cannot be
  /// told apart.
  std::optional<std::vector<CertInt>>
  witnessesOf(const LogicExpr *Q, bool Negated, const CertInt &Low,
              const CertInt &High, bool Bounded) {
    // Unfolding recursive definitions can expose comparisons, or bury them
    // under quantifiers: try none first, then deeper.
    for (unsigned Recursive = 0; Recursive != 3; ++Recursive)
      if (std::optional<std::vector<CertInt>> Witnesses =
              witnessesAt(Q, Negated, Low, High, Bounded, Recursive))
        return Witnesses;
    return std::nullopt;
  }

  std::optional<std::vector<CertInt>>
  witnessesAt(const LogicExpr *Q, bool Negated, const CertInt &Low,
              const CertInt &High, bool Bounded, unsigned Recursive) {
    if (!Failure.empty())
      return std::nullopt;
    std::unique_ptr<LogicExpr> Probe = cloneLogicExpr(Q);
    std::unique_ptr<LogicExpr> &Body = Probe->Children.back();
    if (Negated) {
      auto Not = std::make_unique<LogicExpr>(LogicExpr::Not);
      Not->Sort = LogicSort::boolSort();
      Not->Children.push_back(std::move(Body));
      Body = std::move(Not);
    }
    uint64_t Budget = MaxUnfoldedTerms;
    inlineAt(Body, Q->Binder, 4, Recursive, Budget);
    Steps += MaxUnfoldedTerms - Budget;
    if (!approximate(Body, true, Q->Binder))
      return std::nullopt;
    fold(Body, Q->Binder);
    if (Body->K == LogicExpr::False)
      return std::vector<CertInt>();
    std::optional<std::set<CertInt>> Distinguished =
        distinguishedValues(Probe.get(), Low, High, !Bounded);
    if (!Distinguished)
      return std::nullopt;
    const CertInt Expansion(static_cast<int64_t>(Limits.DirectExpansion));
    std::vector<CertInt> Witnesses;
    auto holds = [&](const CertInt &Binder) -> std::optional<bool> {
      ++Instances;
      Scope.emplace_back(Q->Binder, LogicValue::integer(Binder));
      std::optional<bool> Holds = truthOf(Body.get());
      Scope.pop_back();
      return Holds;
    };
    // Between distinguished values the approximation is constant: a stretch
    // where it holds contributes every value, which must be few.
    auto stretch = [&](const CertInt &From, const CertInt &To,
                       bool Open) -> bool {
      std::optional<bool> Holds = holds(From);
      if (!Holds)
        return false;
      if (!*Holds)
        return true;
      if (Open || Expansion < To - From)
        return false;
      for (CertInt B = From; B < To; B = B + CertInt(1))
        Witnesses.push_back(B);
      return true;
    };
    std::optional<CertInt> Previous;
    for (const CertInt &Value : *Distinguished) {
      if (Bounded && (Value < Low || !(Value < High)))
        continue;
      const CertInt Start = Previous ? *Previous + CertInt(1)
                                     : (Bounded ? Low : Value - CertInt(1));
      if (Start < Value && !stretch(Start, Value, !Previous && !Bounded))
        return std::nullopt;
      std::optional<bool> Holds = holds(Value);
      if (!Holds)
        return std::nullopt;
      if (*Holds)
        Witnesses.push_back(Value);
      Previous = Value;
    }
    const CertInt Start = Previous ? *Previous + CertInt(1) : Low;
    if (!Bounded || Start < High)
      if (!stretch(Start, Bounded ? High : Start + CertInt(1), !Bounded))
        return std::nullopt;
    return Witnesses;
  }

  /// Decides quantifier \p Q by its finitely many witnesses, if it has them.
  std::optional<LogicValue> byWitnesses(const LogicExpr *Q, const CertInt &Low,
                                        const CertInt &High, bool Bounded) {
    const bool Forall = Q->K == LogicExpr::Forall;
    std::optional<std::vector<CertInt>> Witnesses =
        witnessesOf(Q, Forall, Low, High, Bounded);
    if (!Witnesses)
      return std::nullopt;
    return overBinders(Q->Children.back().get(), Q->Binder, *Witnesses, Forall);
  }

  static bool appliesAny(const LogicExpr *E,
                         const std::set<std::string> &Group) {
    if (!E)
      return false;
    if (E->K == LogicExpr::SpecCall && Group.count(E->SpecCallee))
      return true;
    return llvm::any_of(E->Children, [&](const std::unique_ptr<LogicExpr> &C) {
      return appliesAny(C.get(), Group);
    });
  }

  /// A quantifier over premises of the fixpoint being computed. A universal
  /// is bounded and expanded. An existential's witnesses lie where its body
  /// can hold with every premise true; they must be finitely many, found
  /// where the comparisons of that body change.
  std::optional<LogicValue> fixpointQuantifier(const LogicExpr *E) {
    const bool Forall = E->K == LogicExpr::Forall;
    const bool Bounded = E->Children.size() == 3;
    CertInt Low(0), High(0);
    if (Bounded) {
      std::optional<CertInt> L = integerOf(E->Children[0].get());
      if (!L)
        return std::nullopt;
      std::optional<CertInt> H = integerOf(E->Children[1].get());
      if (!H)
        return std::nullopt;
      Low = *L;
      High = *H;
      if (!(Low < High))
        return LogicValue::boolean(Forall);
    }
    auto at = [&](const LogicExpr *Body,
                  const CertInt &Binder) -> std::optional<bool> {
      ++Instances;
      Scope.emplace_back(E->Binder, LogicValue::integer(Binder));
      std::optional<bool> Holds = truthOf(Body);
      Scope.pop_back();
      return Holds;
    };
    const CertInt Expansion(static_cast<int64_t>(Limits.DirectExpansion));
    if (Forall) {
      if (!Bounded || Expansion < High - Low)
        return limit("a universal over premises of an inductive predicate "
                     "has too many values to expand");
      for (CertInt B = Low; B < High; B = B + CertInt(1)) {
        std::optional<bool> Holds = at(E->Children[2].get(), B);
        if (!Holds)
          return std::nullopt;
        if (!*Holds)
          return LogicValue::boolean(false);
      }
      return LogicValue::boolean(true);
    }
    // An existential's witnesses lie where its body can hold with every
    // premise true; they must be finitely many.
    if (std::optional<LogicValue> Decided = byWitnesses(E, Low, High, Bounded))
      return Decided;
    return Failure.empty()
               ? limit("the witnesses of an existential over premises of an "
                       "inductive predicate are not finitely many")
               : std::nullopt;
  }

  /// A bool function's value as its postconditions decide it: the one
  /// value they allow at \p Args.
  std::optional<LogicValue>
  fromPostconditions(const LogicFunctionDecl &Function,
                     const std::vector<LogicValue> &Args) {
    if (Function.ResultSort.Kind != LogicSortKind::Bool ||
        Function.Postconditions.empty() ||
        !PostsInUse.insert(Function.Identity).second)
      return std::nullopt;
    llvm::scope_exit Release([&] { PostsInUse.erase(Function.Identity); });
    bool Allowed[2];
    for (bool Candidate : {false, true}) {
      const size_t SavedBase = ScopeBase;
      const size_t SavedSize = Scope.size();
      ScopeBase = SavedSize;
      for (unsigned I = 0; I != Args.size(); ++I)
        Scope.emplace_back(Function.Parameters[I].Name, Args[I]);
      Scope.emplace_back(LogicFunctionDecl::ResultVariable,
                         LogicValue::boolean(Candidate));
      Active.push_back(&Function);
      bool All = true;
      bool Known = true;
      for (const auto &Post : Function.Postconditions) {
        std::optional<bool> Holds = truthOf(Post.get());
        if (!Holds) {
          Known = false;
          break;
        }
        if (!*Holds) {
          All = false;
          break;
        }
      }
      Active.pop_back();
      Scope.resize(SavedSize);
      ScopeBase = SavedBase;
      if (!Known)
        return std::nullopt;
      Allowed[Candidate] = All;
    }
    if (Allowed[0] == Allowed[1])
      return std::nullopt;
    Evidence.insert(Function.Identity);
    return LogicValue::boolean(Allowed[1]);
  }

  static std::string shown(const LogicFunctionDecl &Function,
                           const std::vector<LogicValue> &Args) {
    std::string Text = displayName(Function) + "(";
    bool First = true;
    for (size_t I = 0; I != Args.size(); ++I) {
      if (Function.Parameters[I].Sort.Kind == LogicSortKind::Heap)
        continue;
      Text += (First ? "" : ", ") + Args[I].key();
      First = false;
    }
    return Text + ")";
  }

  std::optional<LogicValue> definition(const LogicFunctionDecl &Function,
                                       const std::vector<LogicValue> &Args) {
    std::string Key = Function.Identity;
    for (const LogicValue &Argument : Args)
      Key += "\x1f" + Argument.key();
    if (auto It = Applications.find(Key); It != Applications.end())
      return settled(Key, Function, Args, It->second);
    if (auto It = Undecided.find(Key); It != Undecided.end()) {
      LimitInDefinition = true;
      return fail(It->second);
    }
    if (!Function.StepDefinition)
      return fail(Function.DisplayName +
                  " has no definition, so the counterexample relies on a "
                  "value the specification leaves open");
    Computed Result;
    std::optional<LogicValue> Value;
    if (Function.Unfolding) {
      if (std::optional<bool> Least =
              leastFixpoint(Function, Args, Result.Graph))
        Value = LogicValue::boolean(*Least);
      // Its postconditions settle a false value at once, which no search for
      // a derivation can.
      if (!Value && Failure.empty() && !Function.Postconditions.empty()) {
        const bool SavedLimit = LimitInDefinition;
        Value = fromPostconditions(Function, Args);
        Result.ByPostcondition = Value.has_value();
        if (!Value && !spent()) {
          Failure.clear();
          LimitInDefinition = SavedLimit;
        }
      }
    }
    if (!Value && Failure.empty()) {
      // A terminating definition never needs its own value: one that does
      // leaves it open.
      if (!InProgress.insert(Key).second)
        return limit("the definition of " + shown(Function, Args) +
                     " depends on that value itself, so it does not "
                     "determine it");
      const size_t SavedBase = ScopeBase;
      const size_t SavedSize = Scope.size();
      ScopeBase = SavedSize;
      for (unsigned I = 0; I != Args.size(); ++I)
        Scope.emplace_back(Function.Parameters[I].Name, Args[I]);
      Active.push_back(&Function);
      Value = coerce(eval(Function.StepDefinition.get()),
                     Function.StepDefinition->Sort, Function.ResultSort,
                     isSigned(Function.ResultSort));
      Active.pop_back();
      Scope.resize(SavedSize);
      ScopeBase = SavedBase;
      InProgress.erase(Key);
    }
    // Where the definition runs out, a postcondition may still decide the
    // value; the counterexample then rests on it.
    if (!Value && LimitInDefinition && !spent() && !Function.Unfolding &&
        !Function.Postconditions.empty()) {
      const std::string Saved = std::move(Failure);
      Failure.clear();
      Value = fromPostconditions(Function, Args);
      Result.ByPostcondition = Value.has_value();
      if (!Value)
        Failure = Saved;
    }
    if (!Value && Function.Unfolding && LimitInDefinition && !spent())
      Failure = "whether " + shown(Function, Args) +
                " holds: no derivation was found among the heights tried, "
                "its derivations from there do not reach finitely many "
                "arguments, and no postcondition of " +
                displayName(Function) +
                " decides it (a proved one such as !result || Q, with Q "
                "false there, would)";
    if (!Value) {
      // A nesting limit depends on where the application is evaluated.
      if (LimitInDefinition && !spent() &&
          !llvm::StringRef(Failure).starts_with("the evaluation nesting limit"))
        Undecided.emplace(Key, Failure);
      return std::nullopt;
    }
    if (!Result.Graph)
      Result.Node = 0;
    Result.Value = *Value;
    auto [It, Inserted] = Applications.try_emplace(Key, Result);
    std::vector<DefinitionInstance> Facts =
        justification(It->second, Function, Args);
    if (Facts.empty())
      Evaluated.push_back({&Function, Args});
    for (DefinitionInstance &Instance : Facts)
      Evaluated.push_back(std::move(Instance));
    return settled(Key, Function, Args, It->second);
  }

  /// \p Value of an application, compared with the model's, which is a
  /// dispute where they differ.
  std::optional<LogicValue> settled(const std::string &Key,
                                    const LogicFunctionDecl &Function,
                                    const std::vector<LogicValue> &Args,
                                    const Computed &Value) {
    // A model's application can be expensive to read: check the clock first.
    if (pastDeadline())
      return limit("the time limit was reached");
    if (DisputeKeys.count(Key))
      return Value.Value;
    std::optional<LogicValue> Claimed = Model.application(Function, Args);
    if (Claimed && !(*Claimed == Value.Value)) {
      DisputeKeys.insert(Key);
      Disputes.push_back(
          {&Function, Args, justification(Value, Function, Args), false});
    }
    return Value.Value;
  }

  std::optional<LogicValue> application(const LogicExpr *E) {
    const LogicFunctionDecl *Declared = function(E->SpecCallee);
    if (!Declared)
      return fail("no declaration for " + E->SpecCallee);
    const LogicFunctionDecl &Function = *Declared;
    if (E->Children.size() != Function.Parameters.size())
      return fail("argument count mismatch for " + Function.DisplayName);
    std::vector<LogicValue> Args;
    for (unsigned I = 0; I != E->Children.size(); ++I) {
      const LogicSort &Parameter = Function.Parameters[I].Sort;
      std::optional<LogicValue> Argument =
          coerce(eval(E->Children[I].get()), E->Children[I]->Sort, Parameter,
                 isSigned(Parameter));
      if (!Argument)
        return std::nullopt;
      Args.push_back(std::move(*Argument));
    }
    std::optional<LogicValue> Value;
    // A premise of the least fixpoint being computed: its current value.
    if (!Fixpoints.empty() &&
        Fixpoints.back()->Group.count(Function.Identity)) {
      Fixpoint &F = *Fixpoints.back();
      const size_t Node = fixpointNode(F, Function, Args);
      F.Readers[Node].insert(F.Reader);
      F.Reads[F.Reader].insert(Node);
      return coerce(LogicValue::boolean(F.Values[Node]), Function.ResultSort,
                    E->Sort, isSigned(Function.ResultSort));
    }
    // A choice function means any interpretation that satisfies its axioms,
    // which the query assumes: the model's is one.
    if (!Function.Choice &&
        (Mode == View::Definitions || Model.defined(Function))) {
      const bool Closed = Scope.empty() && Active.empty();
      Value = definition(Function, Args);
      if (!Value && Closed && LimitInDefinition && !Deep)
        Deep = E;
    } else {
      if (pastDeadline())
        return limit("the time limit was reached");
      Value = Model.application(Function, Args);
      if (!Value && Failure.empty()) {
        return fail("the model gives no value for an application of " +
                    Function.DisplayName);
      }
    }
    return coerce(std::move(Value), Function.ResultSort, E->Sort,
                  isSigned(Function.ResultSort));
  }

  /// A collection operation, exactly as cppverify.h specifies it.
  std::optional<LogicValue> collection(const LogicExpr *E) {
    std::vector<LogicValue> Operands;
    for (const auto &Child : E->Children) {
      std::optional<LogicValue> Value = eval(Child.get());
      if (!Value)
        return std::nullopt;
      Operands.push_back(std::move(*Value));
    }
    auto integerAt = [&](size_t I) -> const CertInt * {
      return I < Operands.size() && Operands[I].K == LogicValue::Kind::Integer
                 ? &Operands[I].Integer
                 : nullptr;
    };
    auto kindAt = [&](size_t I, LogicValue::Kind Kind) {
      return I < Operands.size() && Operands[I].K == Kind;
    };
    // Sequences are expanded element by element; a length past the budget
    // cannot be checked.
    auto boundedLength = [&](const CertInt &Length) {
      return Length < CertInt(static_cast<int64_t>(Limits.DirectExpansion));
    };
    using Op = LogicCollectionOp;
    using VK = LogicValue::Kind;
    switch (E->CollectionOp) {
    case Op::SeqEmpty:
      return LogicValue::sequence({});
    case Op::SeqUnit:
      if (const CertInt *X = integerAt(0))
        return LogicValue::sequence({*X});
      break;
    case Op::SeqLength:
      if (kindAt(0, VK::Seq))
        return integer(CertInt(
            static_cast<int64_t>(Operands[0].Elements->size())));
      break;
    case Op::SeqIndex: {
      const CertInt *I = integerAt(1);
      if (!kindAt(0, VK::Seq) || !I)
        break;
      const auto &S = *Operands[0].Elements;
      if (I->isNegative() ||
          !(*I < CertInt(static_cast<int64_t>(S.size()))))
        return integer(CertInt(0));
      return integer(S[static_cast<size_t>(I->bits(64).getZExtValue())]);
    }
    case Op::SeqPush: {
      const CertInt *X = integerAt(1);
      if (!kindAt(0, VK::Seq) || !X)
        break;
      std::vector<CertInt> S = *Operands[0].Elements;
      if (!boundedLength(CertInt(static_cast<int64_t>(S.size()))))
        return limit("a sequence is too long to evaluate");
      S.push_back(*X);
      return LogicValue::sequence(std::move(S));
    }
    case Op::SeqSubrange: {
      const CertInt *Lo = integerAt(1);
      const CertInt *Hi = integerAt(2);
      if (!kindAt(0, VK::Seq) || !Lo || !Hi)
        break;
      const auto &S = *Operands[0].Elements;
      const CertInt Length(static_cast<int64_t>(S.size()));
      auto clamp = [&](const CertInt &V, const CertInt &Low) {
        if (V < Low)
          return Low;
        return Length < V ? Length : V;
      };
      const CertInt From = clamp(*Lo, CertInt(0));
      const CertInt To = clamp(*Hi, From);
      return LogicValue::sequence(std::vector<CertInt>(
          S.begin() + From.bits(64).getZExtValue(),
          S.begin() + To.bits(64).getZExtValue()));
    }
    case Op::SeqConcat: {
      if (!kindAt(0, VK::Seq) || !kindAt(1, VK::Seq))
        break;
      std::vector<CertInt> S = *Operands[0].Elements;
      const auto &T = *Operands[1].Elements;
      if (!boundedLength(CertInt(static_cast<int64_t>(S.size() + T.size()))))
        return limit("a sequence is too long to evaluate");
      S.insert(S.end(), T.begin(), T.end());
      return LogicValue::sequence(std::move(S));
    }
    case Op::SeqContains: {
      const CertInt *X = integerAt(1);
      if (!kindAt(0, VK::Seq) || !X)
        break;
      const auto &S = *Operands[0].Elements;
      return LogicValue::boolean(std::find(S.begin(), S.end(), *X) != S.end());
    }
    case Op::SetEmpty:
      return LogicValue::set(HeapValue{});
    case Op::SetInsert:
    case Op::SetRemove: {
      const CertInt *X = integerAt(1);
      if (!kindAt(0, VK::Set) || !X)
        break;
      HeapValue Members = *Operands[0].Heap;
      Members.set(*X, CertInt(E->CollectionOp == Op::SetInsert ? 1 : 0));
      return LogicValue::set(std::move(Members));
    }
    case Op::SetContains: {
      const CertInt *X = integerAt(1);
      if (!kindAt(0, VK::Set) || !X)
        break;
      return LogicValue::boolean(!Operands[0].Heap->get(*X).isZero());
    }
    case Op::SetUnion:
    case Op::SetIntersect:
    case Op::SetDifference: {
      if (!kindAt(0, VK::Set) || !kindAt(1, VK::Set))
        break;
      const Op Which = E->CollectionOp;
      return LogicValue::set(HeapValue::combine(
          *Operands[0].Heap, *Operands[1].Heap,
          [Which](const CertInt &L, const CertInt &R) {
            const bool In = !L.isZero(), Other = !R.isZero();
            const bool Result = Which == Op::SetUnion       ? In || Other
                                : Which == Op::SetIntersect ? In && Other
                                                            : In && !Other;
            return CertInt(Result ? 1 : 0);
          }));
    }
    case Op::SetSubset: {
      if (!kindAt(0, VK::Set) || !kindAt(1, VK::Set))
        break;
      const HeapValue Outside = HeapValue::combine(
          *Operands[0].Heap, *Operands[1].Heap,
          [](const CertInt &L, const CertInt &R) {
            return CertInt(!L.isZero() && R.isZero() ? 1 : 0);
          });
      return LogicValue::boolean(Outside.Default.isZero() &&
                                 Outside.Breaks.empty());
    }
    case Op::MultisetEmpty:
      return LogicValue::multiset(HeapValue{});
    case Op::MultisetInsert:
    case Op::MultisetRemove: {
      const CertInt *X = integerAt(1);
      if (!kindAt(0, VK::Multiset) || !X)
        break;
      HeapValue Counts = *Operands[0].Heap;
      const CertInt Count = Counts.get(*X);
      if (E->CollectionOp == Op::MultisetInsert)
        Counts.set(*X, Count + CertInt(1));
      else if (!Count.isZero())
        Counts.set(*X, Count - CertInt(1));
      return LogicValue::multiset(std::move(Counts));
    }
    case Op::MultisetCount: {
      const CertInt *X = integerAt(1);
      if (!kindAt(0, VK::Multiset) || !X)
        break;
      return integer(Operands[0].Heap->get(*X));
    }
    case Op::MapEmpty:
      return LogicValue::map(HeapValue{}, HeapValue{});
    case Op::MapInsert:
    case Op::MapRemove: {
      const CertInt *K = integerAt(1);
      if (!kindAt(0, VK::Map) || !K)
        break;
      HeapValue Domain = *Operands[0].Heap;
      HeapValue Values = *Operands[0].Values;
      if (E->CollectionOp == Op::MapInsert) {
        const CertInt *V = integerAt(2);
        if (!V)
          break;
        Domain.set(*K, CertInt(1));
        Values.set(*K, *V);
      } else {
        Domain.set(*K, CertInt(0));
        Values.set(*K, CertInt(0));
      }
      return LogicValue::map(std::move(Domain), std::move(Values));
    }
    case Op::MapContains: {
      const CertInt *K = integerAt(1);
      if (!kindAt(0, VK::Map) || !K)
        break;
      return LogicValue::boolean(!Operands[0].Heap->get(*K).isZero());
    }
    case Op::MapGet: {
      const CertInt *K = integerAt(1);
      if (!kindAt(0, VK::Map) || !K)
        break;
      return integer(Operands[0].Values->get(*K));
    }
    }
    return fail(std::string("malformed collection operation ") +
                logicCollectionOpName(E->CollectionOp));
  }

  /// Both heaps are constant between their breakpoints, so they differ on
  /// whole segments, each of which must lie inside the frame's regions.
  std::optional<LogicValue> heapFrame(const LogicExpr *E) {
    std::optional<LogicValue> Before = eval(E->Children[0].get());
    if (!Before)
      return std::nullopt;
    std::optional<LogicValue> After = eval(E->Children[1].get());
    if (!After)
      return std::nullopt;
    if (Before->K != LogicValue::Kind::Heap ||
        After->K != LogicValue::Kind::Heap)
      return fail("a frame relates non-heap values");
    std::vector<std::pair<CertInt, CertInt>> Regions;
    for (size_t I = 2; I + 1 < E->Children.size(); I += 2) {
      std::optional<CertInt> Lo = integerOf(E->Children[I].get());
      if (!Lo)
        return std::nullopt;
      std::optional<CertInt> Hi = integerOf(E->Children[I + 1].get());
      if (!Hi)
        return std::nullopt;
      if (*Lo < *Hi)
        Regions.emplace_back(std::move(*Lo), std::move(*Hi));
    }
    llvm::sort(Regions, [](const auto &L, const auto &R) {
      return L.first < R.first;
    });
    std::vector<std::pair<CertInt, CertInt>> Merged;
    for (auto &Region : Regions) {
      if (!Merged.empty() && !(Merged.back().second < Region.first)) {
        if (Merged.back().second < Region.second)
          Merged.back().second = Region.second;
        continue;
      }
      Merged.push_back(std::move(Region));
    }
    auto covered = [&](const CertInt &Lo, const CertInt &Hi) {
      return llvm::any_of(Merged, [&](const auto &Region) {
        return !(Lo < Region.first) && !(Region.second < Hi);
      });
    };
    const HeapValue &B = *Before->Heap;
    const HeapValue &A = *After->Heap;
    if (!(A.Default == B.Default))
      return LogicValue::boolean(false);
    std::set<CertInt> Points;
    for (const auto &Break : A.Breaks)
      Points.insert(Break.first);
    for (const auto &Break : B.Breaks)
      Points.insert(Break.first);
    for (auto It = Points.begin(); It != Points.end(); ++It) {
      if (A.get(*It) == B.get(*It))
        continue;
      auto Next = std::next(It);
      if (Next == Points.end() || !covered(*It, *Next))
        return LogicValue::boolean(false);
    }
    return LogicValue::boolean(true);
  }

  /// Whether evaluating \p E may unfold a definition or expand a quantifier.
  static bool costly(const LogicExpr *E) {
    if (E->K == LogicExpr::SpecCall || E->K == LogicExpr::Forall ||
        E->K == LogicExpr::Exists)
      return true;
    return llvm::any_of(E->Children,
                        [](const std::unique_ptr<LogicExpr> &Child) {
                          return costly(Child.get());
                        });
  }

  /// A conjunction or disjunction in Kleene's strong logic: an operand that
  /// decides it does so whatever the others are, so cheap operands go
  /// first, the others are searched fairly, and one that cannot be decided
  /// settles nothing unless no operand does.
  std::optional<LogicValue> connective(const LogicExpr *E) {
    const bool Deciding = E->K == LogicExpr::Or;
    std::vector<const LogicExpr *> Costly;
    for (const auto &Child : E->Children) {
      if (costly(Child.get())) {
        Costly.push_back(Child.get());
        continue;
      }
      std::optional<bool> Holds = truthOf(Child.get());
      if (!Holds)
        return std::nullopt;
      if (*Holds == Deciding)
        return LogicValue::boolean(Deciding);
    }
    if (Costly.size() == 1) {
      std::optional<bool> Holds = truthOf(Costly.front());
      if (!Holds)
        return std::nullopt;
      return LogicValue::boolean(*Holds);
    }
    std::optional<bool> Decided = fairly(
        Costly.size(), [&](size_t I) { return truthOf(Costly[I]); }, Deciding);
    if (!Decided)
      return std::nullopt;
    return LogicValue::boolean(*Decided ? Deciding : !Deciding);
  }

  std::optional<LogicValue> evalNode(const LogicExpr *E) {
    switch (E->K) {
    case LogicExpr::True:
      return LogicValue::boolean(true);
    case LogicExpr::False:
      return LogicValue::boolean(false);
    case LogicExpr::BoolLit:
      return LogicValue::boolean(E->BoolVal);
    case LogicExpr::IntLit: {
      std::optional<CertInt> Value = CertInt::fromDecimal(E->IntVal);
      if (!Value)
        return fail("malformed integer literal");
      if (E->Sort.Kind == LogicSortKind::BitVector)
        return LogicValue::integer(reduce(*Value, E->Sort));
      return integer(*Value);
    }
    case LogicExpr::Var:
      return lookup(E);
    case LogicExpr::Not: {
      std::optional<bool> Holds = truthOf(E->Children[0].get());
      if (!Holds)
        return std::nullopt;
      return LogicValue::boolean(!*Holds);
    }
    case LogicExpr::And:
    case LogicExpr::Or:
      return connective(E);
    case LogicExpr::Ite: {
      std::optional<bool> Condition = truthOf(E->Children[0].get());
      if (!Condition)
        return std::nullopt;
      const LogicExpr *Branch = E->Children[*Condition ? 1 : 2].get();
      return coerce(eval(Branch), Branch->Sort, E->Sort, isSigned(E->Sort));
    }
    case LogicExpr::Eq:
    case LogicExpr::Ne:
    case LogicExpr::Lt:
    case LogicExpr::Le:
    case LogicExpr::Gt:
    case LogicExpr::Ge:
    case LogicExpr::Add:
    case LogicExpr::Sub:
    case LogicExpr::Mul:
    case LogicExpr::Div:
    case LogicExpr::Rem:
    case LogicExpr::BitAnd:
    case LogicExpr::BitOr:
    case LogicExpr::BitXor:
    case LogicExpr::Shl:
    case LogicExpr::Shr:
      return binary(E);
    case LogicExpr::Neg: {
      std::optional<CertInt> Value = integerOf(E->Children[0].get());
      if (!Value)
        return std::nullopt;
      if (E->Sort.Kind == LogicSortKind::BitVector)
        return LogicValue::integer(reduce(-*Value, E->Sort));
      return integer(-*Value);
    }
    case LogicExpr::BitNot: {
      std::optional<CertInt> Value = integerOf(E->Children[0].get());
      if (!Value)
        return std::nullopt;
      return LogicValue::integer(isSigned(E->Sort)
                                     ? -*Value - CertInt(1)
                                     : CertInt::powerOfTwo(E->Sort.BitWidth) -
                                           CertInt(1) - *Value);
    }
    case LogicExpr::ValidPtr: {
      std::optional<CertInt> Address = integerOf(E->Children[0].get());
      if (!Address)
        return std::nullopt;
      std::optional<bool> Valid = Model.validPointer(*Address);
      if (!Valid)
        return fail("the model gives no pointer validity");
      return LogicValue::boolean(*Valid);
    }
    case LogicExpr::Select: {
      std::optional<LogicValue> Heap = eval(E->Children[0].get());
      if (!Heap)
        return std::nullopt;
      std::optional<CertInt> Address = integerOf(E->Children[1].get());
      if (!Address)
        return std::nullopt;
      if (Heap->K != LogicValue::Kind::Heap)
        return fail("a load reads a non-heap value");
      const CertInt &Cell = Heap->Heap->get(*Address);
      switch (E->Sort.Kind) {
      case LogicSortKind::Bool:
        return LogicValue::boolean(!Cell.isZero());
      case LogicSortKind::BitVector:
        return LogicValue::integer(reduce(Cell, E->Sort));
      case LogicSortKind::MathematicalInteger:
      case LogicSortKind::Pointer:
        return LogicValue::integer(Cell);
      default:
        return fail("a load has an unsupported sort");
      }
    }
    case LogicExpr::Store: {
      std::optional<LogicValue> Before = eval(E->Children[0].get());
      if (!Before)
        return std::nullopt;
      std::optional<CertInt> Address = integerOf(E->Children[1].get());
      if (!Address)
        return std::nullopt;
      std::optional<LogicValue> Stored = eval(E->Children[2].get());
      if (!Stored)
        return std::nullopt;
      std::optional<LogicValue> After = eval(E->Children[3].get());
      if (!After)
        return std::nullopt;
      if (Before->K != LogicValue::Kind::Heap ||
          After->K != LogicValue::Kind::Heap)
        return fail("a store relates non-heap values");
      // Cells hold the unsigned bit pattern of a machine value.
      const LogicSort &StoredSort = E->Children[2]->Sort;
      CertInt Cell;
      if (Stored->K == LogicValue::Kind::Bool)
        Cell = CertInt(Stored->Truth ? 1 : 0);
      else if (Stored->K != LogicValue::Kind::Integer)
        return fail("a store writes a heap value");
      else if (StoredSort.Kind == LogicSortKind::BitVector)
        Cell = reinterpret(Stored->Integer, StoredSort.BitWidth,
                           isSigned(StoredSort), false);
      else
        Cell = Stored->Integer;
      HeapValue Updated = *Before->Heap;
      Updated.set(*Address, Cell);
      return LogicValue::boolean(Updated == *After->Heap);
    }
    case LogicExpr::HeapFrame:
      return heapFrame(E);
    case LogicExpr::Collection:
      return collection(E);
    case LogicExpr::Forall:
    case LogicExpr::Exists:
      return quantifier(E);
    case LogicExpr::IntToBv: {
      std::optional<CertInt> Value = integerOf(E->Children[0].get());
      if (!Value)
        return std::nullopt;
      return LogicValue::integer(reduce(*Value, E->Sort));
    }
    case LogicExpr::BvToInt:
      return eval(E->Children[0].get());
    case LogicExpr::BvResize: {
      std::optional<CertInt> Value = integerOf(E->Children[0].get());
      if (!Value)
        return std::nullopt;
      return LogicValue::integer(
          convertMachine(*Value, E->Children[0]->Sort, E->Sort));
    }
    case LogicExpr::NoOverflow:
      return noOverflow(E);
    case LogicExpr::SpecCall:
      return application(E);
    }
    return fail("unsupported term");
  }

  bool pastDeadline() const {
    return Limits.Deadline &&
           std::chrono::steady_clock::now() >= *Limits.Deadline;
  }

public:
  Evaluator(const ObligationModule &Module, CandidateModel &Model,
            const CertifyLimits &Limits, View Mode)
      : Module(Module), Model(Model), Limits(Limits), Mode(Mode) {}

  std::optional<LogicValue> eval(const LogicExpr *E) {
    if (!Failure.empty())
      return std::nullopt;
    if (!E)
      return fail("null term");
    if (++Steps > Limits.Steps) {
      Exhausted = true;
      return limit("the evaluation step limit was reached");
    }
    if (Exhausted || (NextClockCheck <= Steps && pastDeadline())) {
      Exhausted = true;
      return limit("the time limit was reached");
    }
    if (NextClockCheck <= Steps)
      NextClockCheck = Steps + 4096;
    if (SliceEnd < Steps) {
      SliceSpent = true;
      return fail("the evaluation slice was spent");
    }
    if (Frames >= Limits.Frames)
      return limit("the evaluation nesting limit was reached");
    ++Frames;
    std::optional<LogicValue> Value = evalNode(E);
    --Frames;
    return Value;
  }

  /// Whether the model keeps \p Instance, evaluated in the model's view;
  /// nullopt when that cannot be told.
  std::optional<bool> keeps(const DefinitionInstance &Instance) {
    Failure.clear();
    const LogicFunctionDecl &Function = *Instance.Function;
    if (Model.defined(Function))
      return true;
    std::optional<LogicValue> Applied =
        Model.application(Function, Instance.Arguments);
    if (!Applied)
      return std::nullopt;
    const size_t SavedBase = ScopeBase;
    const size_t SavedSize = Scope.size();
    ScopeBase = SavedSize;
    for (unsigned I = 0; I != Instance.Arguments.size(); ++I)
      Scope.emplace_back(Function.Parameters[I].Name, Instance.Arguments[I]);
    std::optional<bool> Kept;
    switch (Instance.Of) {
    case DefinitionInstance::Kind::Definition:
    case DefinitionInstance::Kind::Unfolding: {
      const LogicExpr *Body = Instance.Of == DefinitionInstance::Kind::Unfolding
                                  ? Function.Unfolding.get()
                                  : Function.StepDefinition.get();
      if (std::optional<LogicValue> Value =
              Body ? coerce(eval(Body), Body->Sort, Function.ResultSort,
                            isSigned(Function.ResultSort))
                   : std::nullopt)
        Kept = *Value == *Applied;
      break;
    }
    case DefinitionInstance::Kind::Postcondition: {
      Scope.emplace_back(LogicFunctionDecl::ResultVariable, *Applied);
      Kept = true;
      for (const auto &Post : Function.Postconditions) {
        std::optional<bool> Holds = truthOf(Post.get());
        if (!Holds) {
          Kept.reset();
          break;
        }
        if (!*Holds) {
          Kept = false;
          break;
        }
      }
      break;
    }
    }
    Scope.resize(SavedSize);
    ScopeBase = SavedBase;
    Failure.clear();
    return Kept;
  }

  const std::string &failure() const { return Failure; }
  bool limitInDefinition() const { return LimitInDefinition; }
  const LogicExpr *wideQuantifier() const { return Wide; }
  const LogicExpr *deepApplication() const { return Deep; }
  std::vector<SpecDispute> takeDisputes() { return std::move(Disputes); }
  const std::set<std::string> &evidence() const { return Evidence; }
  std::vector<DefinitionInstance> takeEvaluated() {
    return std::move(Evaluated);
  }
};

/// No symbol has a value: only closed terms evaluate.
class NoModel : public CandidateModel {
public:
  std::optional<LogicValue> constant(const std::string &,
                                     const LogicSort &) override {
    return std::nullopt;
  }
  std::optional<bool> validPointer(const CertInt &) override {
    return std::nullopt;
  }
  std::optional<LogicValue>
  application(const LogicFunctionDecl &,
              const std::vector<LogicValue> &) override {
    return std::nullopt;
  }
};

bool mentionsSymbol(const LogicExpr *Root) {
  std::vector<const LogicExpr *> Work{Root};
  while (!Work.empty()) {
    const LogicExpr *E = Work.back();
    Work.pop_back();
    if (!E)
      continue;
    if (E->K == LogicExpr::Var || E->K == LogicExpr::ValidPtr)
      return true;
    for (const auto &Child : E->Children)
      Work.push_back(Child.get());
  }
  return false;
}

std::string joinNames(const std::set<std::string> &Names) {
  std::string List;
  for (const std::string &Name : Names)
    List += (List.empty() ? "" : ", ") + Name;
  return List;
}

constexpr unsigned CertifierStackBytes = 256U << 20;

} // namespace

CertifyResult verify::certifyCounterexample(const ObligationModule &Module,
                                            const LogicExpr &Query,
                                            CandidateModel &Model,
                                            const CertifyLimits &Limits) {
  CertifyResult Result;
  auto Run = [&] {
    Evaluator Definitions(Module, Model, Limits, View::Definitions);
    std::optional<LogicValue> Holds = Definitions.eval(&Query);
    if (!Holds || Holds->K != LogicValue::Kind::Bool) {
      Result.Outcome = CertifyOutcome::Undetermined;
      Result.Detail =
          Holds ? "the query is not a formula" : Definitions.failure();
      Result.DefinitionTooDeep = !Holds && Definitions.limitInDefinition();
      Result.WideQuantifier = Definitions.wideQuantifier();
      if (Result.DefinitionTooDeep)
        Result.DeepApplication = Definitions.deepApplication();
      return;
    }
    if (Holds->Truth) {
      Result.Outcome = CertifyOutcome::Certified;
      Result.Evidence = Definitions.evidence();
      return;
    }
    Evaluator Claimed(Module, Model, Limits, View::Model);
    std::optional<LogicValue> Satisfied = Claimed.eval(&Query);
    std::vector<SpecDispute> Disputes = Definitions.takeDisputes();
    // The definitions refute the model. Its own view only tells a wrong
    // answer from a dispute; where it leaves a value open, the disputes
    // still refine the search.
    if (!Satisfied || Satisfied->K != LogicValue::Kind::Bool) {
      if (Satisfied || Disputes.empty()) {
        Result.Outcome = CertifyOutcome::Undetermined;
        Result.Detail =
            Satisfied ? "the query is not a formula" : Claimed.failure();
        Result.WideQuantifier = Claimed.wideQuantifier();
        return;
      }
      Satisfied = LogicValue::boolean(true);
    }
    // Each dispute's facts, checked in the model's own view: one the model
    // breaks can only have been ignored if the solver was given it.
    for (SpecDispute &Dispute : Disputes) {
      std::vector<DefinitionInstance> Facts = Dispute.Justification;
      if (Facts.empty())
        Facts.push_back({Dispute.Function, Dispute.Arguments});
      for (const DefinitionInstance &Fact : Facts)
        if (Claimed.keeps(Fact) == std::optional<bool>(false)) {
          Dispute.Violated = true;
          break;
        }
    }
    if (!Satisfied->Truth || Disputes.empty()) {
      Result.Outcome = CertifyOutcome::Inconsistent;
      Result.Detail = !Satisfied->Truth
                          ? "the model does not satisfy the query"
                          : "the query fails although every application "
                            "agrees with its definition";
      return;
    }
    Result.Outcome = CertifyOutcome::Disputed;
    Result.Disputes = std::move(Disputes);
  };
  llvm::thread Worker(std::optional<unsigned>(CertifierStackBytes), Run);
  Worker.join();
  return Result;
}

std::optional<LogicValue> verify::evaluateTerm(const ObligationModule &Module,
                                               const LogicExpr &Term,
                                               CandidateModel &Model,
                                               const CertifyLimits &Limits,
                                               std::string *Failure) {
  std::optional<LogicValue> Value;
  auto Run = [&] {
    Evaluator Definitions(Module, Model, Limits, View::Definitions);
    Value = Definitions.eval(&Term);
    if (!Value && Failure)
      *Failure = Definitions.failure();
  };
  llvm::thread Worker(std::optional<unsigned>(CertifierStackBytes), Run);
  Worker.join();
  return Value;
}

std::vector<DefinitionInstance>
verify::closedApplicationInstances(const ObligationModule &Module,
                                   const LogicExpr &Query,
                                   const CertifyLimits &Limits) {
  std::vector<const LogicExpr *> Closed;
  std::vector<const LogicExpr *> Work{&Query};
  while (!Work.empty()) {
    const LogicExpr *E = Work.back();
    Work.pop_back();
    if (!E)
      continue;
    if (E->K == LogicExpr::SpecCall && !mentionsSymbol(E)) {
      Closed.push_back(E);
      continue;
    }
    for (const auto &Child : E->Children)
      Work.push_back(Child.get());
  }
  std::vector<DefinitionInstance> Instances;
  if (Closed.empty())
    return Instances;
  auto Run = [&] {
    std::set<std::string> Seen;
    NoModel Model;
    for (const LogicExpr *Call : Closed) {
      Evaluator Definitions(Module, Model, Limits, View::Definitions);
      if (!Definitions.eval(Call))
        continue;
      std::vector<DefinitionInstance> Reached = Definitions.takeEvaluated();
      if (Instances.size() + Reached.size() >
          DefinitionRefinement::MaxInstances)
        continue;
      for (DefinitionInstance &Instance : Reached)
        if ((Instance.Of != DefinitionInstance::Kind::Definition ||
             Instance.Function->DefinitionFuel != 0) &&
            Seen.insert(Instance.key()).second)
          Instances.push_back(std::move(Instance));
    }
  };
  llvm::thread Worker(std::optional<unsigned>(CertifierStackBytes), Run);
  Worker.join();
  recordGivenFacts(Module, Instances);
  return Instances;
}

std::set<std::string>
verify::nonRecursiveDefinitions(const ObligationModule &Module) {
  std::map<std::string, std::set<std::string>> Callees;
  for (const auto &[Identity, Function] : Module.LogicFunctions) {
    std::set<std::string> &Direct = Callees[Identity];
    std::vector<const LogicExpr *> Work{Function.StepDefinition.get()};
    while (!Work.empty()) {
      const LogicExpr *E = Work.back();
      Work.pop_back();
      if (!E)
        continue;
      if (E->K == LogicExpr::SpecCall)
        Direct.insert(E->SpecCallee);
      for (const auto &Child : E->Children)
        Work.push_back(Child.get());
    }
  }
  std::set<std::string> NonRecursive;
  for (const auto &[Identity, Function] : Module.LogicFunctions) {
    if (!Function.StepDefinition)
      continue;
    std::set<std::string> Reached;
    std::vector<std::string> Work{Identity};
    while (!Work.empty() && !Reached.count(Identity)) {
      const std::string Current = std::move(Work.back());
      Work.pop_back();
      auto It = Callees.find(Current);
      if (It == Callees.end())
        continue;
      for (const std::string &Callee : It->second)
        if (Reached.insert(Callee).second)
          Work.push_back(Callee);
    }
    if (!Reached.count(Identity))
      NonRecursive.insert(Identity);
  }
  return NonRecursive;
}

RefinementDecision DefinitionRefinement::next(const CertifyResult &Result,
                                              bool BoundedDomain) {
  RefinementDecision Decision;
  switch (Result.Outcome) {
  case CertifyOutcome::Certified:
    Decision.Next = RefinementDecision::Action::Report;
    return Decision;
  case CertifyOutcome::Undetermined:
    if (Result.DefinitionTooDeep) {
      Decision.Unbounded = true;
      Decision.Reason = VerifyReason::SpecFuel;
      Decision.Message = "checking the counterexample needs a definition "
                         "evaluated beyond the certifier's limits (" +
                         Result.Detail +
                         "); bound the argument, or prove the property by "
                         "induction in a proof function";
      return Decision;
    }
    Decision.Reason = VerifyReason::UncheckedCounterexample;
    Decision.Message = "the counterexample could not be checked against the "
                       "definitions: " +
                       Result.Detail;
    return Decision;
  case CertifyOutcome::Inconsistent:
    Decision.Reason = VerifyReason::InvalidBackendResult;
    Decision.Message = "the solver's model contradicts the obligation "
                       "semantics: " +
                       Result.Detail;
    return Decision;
  case CertifyOutcome::Disputed:
    break;
  }
  bool OnlyHidden = true;
  bool Violated = false;
  const SpecDispute *Stalled = nullptr;
  for (const SpecDispute &Dispute : Result.Disputes) {
    const LogicFunctionDecl &Function = *Dispute.Function;
    Disputed.insert(displayName(Function));
    std::vector<DefinitionInstance> Facts = Dispute.Justification;
    if (Facts.empty())
      Facts.push_back({&Function, Dispute.Arguments});
    bool New = false;
    for (DefinitionInstance &Fact : Facts) {
      if (!Given.insert(Fact.key()).second)
        continue;
      New = true;
      // Only a hidden definition steers without proving: unfoldings and
      // proved postconditions are theorems.
      if (Fact.Of == DefinitionInstance::Kind::Definition &&
          Fact.Function->DefinitionFuel == 0)
        HiddenGiven.insert(displayName(*Fact.Function));
      else
        OnlyHidden = false;
      Decision.Instances.push_back(std::move(Fact));
    }
    if (!New) {
      Violated = Violated || Dispute.Violated;
      if (!Dispute.Justification.empty() && !Stalled)
        Stalled = &Dispute;
    }
  }
  if (Decision.Instances.empty()) {
    // Every fact was given before. A model that breaks one is a wrong
    // answer; otherwise the value follows from no finite set of instances.
    if (Violated) {
      Decision.Reason = VerifyReason::InvalidBackendResult;
      Decision.Message = "the solver's model contradicts definition instances "
                         "it was given";
      return Decision;
    }
    Decision.Reason = VerifyReason::SpecFuel;
    if (Stalled && Stalled->Function->Unfolding) {
      Decision.Unbounded = true;
      Decision.InductionOnly = true;
      std::string Application = displayName(*Stalled->Function) + "(";
      bool First = true;
      for (size_t I = 0; I != Stalled->Arguments.size(); ++I) {
        if (Stalled->Function->Parameters[I].Sort.Kind == LogicSortKind::Heap)
          continue;
        Application += (First ? "" : ", ") + Stalled->Arguments[I].key();
        First = false;
      }
      Application += ")";
      Decision.Message =
          "every counterexample found needs " + Application +
          " to hold, but no derivation shows it: its derivations from there "
          "never reach a base case, and only induction over derivations, not "
          "unfolding, shows that; state what they satisfy as a postcondition "
          "of " +
          displayName(*Stalled->Function) + " (!result || Q)";
    } else {
      Decision.Message = "every counterexample found applies " +
                         joinNames(Disputed) +
                         " where its definition, unfolded at every disputed "
                         "argument, does not settle the value; prove the "
                         "property by induction in a proof function";
    }
    return Decision;
  }
  if (Decision.Instances.size() >
      (BoundedDomain ? MaxInstances : MaxRoundInstances)) {
    RefinementDecision Deep = exhausted();
    Deep.Unbounded = true;
    if (Deep.Reason == VerifyReason::SpecFuel)
      Deep.Message =
          "every counterexample found needs " + joinNames(Disputed) +
          " unfolded at ever larger arguments (the last one needed " +
          std::to_string(Decision.Instances.size()) +
          " unfoldings), so no finite unfolding settles it; prove it by "
          "induction in a proof function whose decreases clause shrinks on "
          "each recursive call, and call that lemma here";
    return Deep;
  }
  if (++Rounds > MaxRounds || Given.size() > MaxInstances ||
      (OnlyHidden && ++HiddenRounds > MaxHiddenRounds))
    return exhausted();
  recordGivenFacts(Module, Decision.Instances);
  Decision.Next = RefinementDecision::Action::Refine;
  return Decision;
}

void verify::recordGivenFacts(
    const ObligationModule &Module,
    const std::vector<DefinitionInstance> &Instances) {
  if (!Module.Given)
    return;
  std::lock_guard<std::mutex> Guard(Module.Given->Lock);
  for (const DefinitionInstance &Instance : Instances) {
    if (Instance.Of == DefinitionInstance::Kind::Unfolding)
      Module.Given->Unfoldings.insert(Instance.Function->Identity);
    else if (Instance.Of == DefinitionInstance::Kind::Postcondition)
      Module.Given->Postconditions.insert(Instance.Function->Identity);
  }
}

std::optional<RefinementDecision> DefinitionRefinement::unsatisfiable() const {
  if (HiddenGiven.empty())
    return std::nullopt;
  RefinementDecision Decision;
  Decision.Reason = VerifyReason::SpecHidden;
  Decision.NoCounterexample = true;
  Decision.Message = "no counterexample exists, but the proof needs the "
                     "definition of " +
                     joinNames(HiddenGiven) +
                     ", which is hidden from the solver; reveal it or state "
                     "a lemma";
  return Decision;
}

RefinementDecision
DefinitionRefinement::exhausted(llvm::StringRef Detail) const {
  RefinementDecision Decision;
  const bool OnlyHidden =
      !Disputed.empty() && llvm::all_of(Disputed, [&](const std::string &Name) {
        return HiddenGiven.count(Name);
      });
  if (OnlyHidden) {
    Decision.Reason = VerifyReason::SpecHidden;
    Decision.Message = "every counterexample found relies on a value of " +
                       joinNames(Disputed) +
                       ", whose definition is hidden from the solver";
    if (!Detail.empty())
      Decision.Message += " (" + Detail.str() + ")";
    Decision.Message += "; reveal it or state a lemma";
    return Decision;
  }
  Decision.Reason = VerifyReason::SpecFuel;
  Decision.Message = "every counterexample found applies " +
                     joinNames(Disputed) +
                     " beyond its unfolding fuel and is refuted by its "
                     "definition";
  if (!Detail.empty())
    Decision.Message += " (" + Detail.str() + ")";
  Decision.Message += "; raise reveal_with_fuel, bound the argument, or prove "
                      "it by induction in a proof function";
  return Decision;
}
