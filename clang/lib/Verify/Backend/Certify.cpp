//===--- Certify.cpp ------------------------------------------------------===//
#include "Certify.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/Support/thread.h"
#include <algorithm>

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
  std::string Key = Function ? Function->Identity : std::string();
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
  std::map<std::string, LogicValue> Applications;
  std::vector<SpecDispute> Disputes;
  std::set<std::string> DisputeKeys;
  std::vector<DefinitionInstance> Evaluated;

  std::nullopt_t fail(std::string Message) {
    if (Failure.empty())
      Failure = std::move(Message);
    return std::nullopt;
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

  /// Over all integers: the distinguished values, one value between each
  /// two, and one beyond each end, where the body is constant.
  std::optional<LogicValue> unboundedQuantifier(const LogicExpr *E) {
    const bool Forall = E->K == LogicExpr::Forall;
    std::optional<std::set<CertInt>> Distinguished =
        distinguishedValues(E, CertInt(0), CertInt(0), /*Unbounded=*/true);
    if (!Distinguished) {
      if (!Failure.empty())
        return std::nullopt;
      return limit("an unbounded quantifier whose body depends on its binder "
                   "other than through loads and comparisons");
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
    for (const CertInt &Binder : Checked) {
      ++Instances;
      Scope.emplace_back(E->Binder, LogicValue::integer(Binder));
      std::optional<bool> Holds = truthOf(E->Children[0].get());
      Scope.pop_back();
      if (!Holds)
        return std::nullopt;
      if (*Holds != Forall)
        return LogicValue::boolean(!Forall);
    }
    return LogicValue::boolean(Forall);
  }

  std::optional<LogicValue> quantifier(const LogicExpr *E) {
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
    auto instance = [&](const CertInt &Binder) {
      Scope.emplace_back(E->Binder, LogicValue::integer(Binder));
      std::optional<bool> Holds = truthOf(E->Children[2].get());
      Scope.pop_back();
      return Holds;
    };
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
        for (const CertInt &Binder : Checked) {
          std::optional<bool> Holds = instance(Binder);
          if (!Holds)
            return std::nullopt;
          if (*Holds != Forall)
            return LogicValue::boolean(!Forall);
        }
        return LogicValue::boolean(Forall);
      }
      if (!Failure.empty())
        return std::nullopt;
    }
    const uint64_t Remaining = Limits.QuantifierInstances -
                               std::min(Instances, Limits.QuantifierInstances);
    if (CertInt(static_cast<int64_t>(
            std::min<uint64_t>(Remaining, INT64_MAX))) < Count) {
      // One instance still decides a range too wide to expand.
      const bool Closed = Scope.empty() && Active.empty();
      for (unsigned I = 0; I != Limits.QuantifierProbe; ++I)
        for (const CertInt &Binder :
             {*Low + CertInt(I), *High - CertInt(1) - CertInt(I)}) {
          std::optional<bool> Holds = instance(Binder);
          if (!Holds)
            return std::nullopt;
          if (*Holds != Forall)
            return LogicValue::boolean(!Forall);
        }
      if (Closed)
        Wide = E;
      return limit("a quantifier range of " + Count.toDecimal() +
                   " values is too wide to expand");
    }
    for (CertInt Binder = *Low; Binder < *High; Binder = Binder + CertInt(1)) {
      ++Instances;
      std::optional<bool> Holds = instance(Binder);
      if (!Holds)
        return std::nullopt;
      if (*Holds != Forall)
        return LogicValue::boolean(!Forall);
    }
    return LogicValue::boolean(Forall);
  }

  std::optional<LogicValue> definition(const LogicFunctionDecl &Function,
                                       const std::vector<LogicValue> &Args) {
    std::string Key = Function.Identity;
    for (const LogicValue &Argument : Args)
      Key += "\x1f" + Argument.key();
    if (auto It = Applications.find(Key); It != Applications.end())
      return It->second;
    if (!Function.StepDefinition)
      return fail(Function.DisplayName +
                  " has no definition, so the counterexample relies on a "
                  "value the specification leaves open");
    const size_t SavedBase = ScopeBase;
    const size_t SavedSize = Scope.size();
    ScopeBase = SavedSize;
    for (unsigned I = 0; I != Args.size(); ++I)
      Scope.emplace_back(Function.Parameters[I].Name, Args[I]);
    Active.push_back(&Function);
    std::optional<LogicValue> Value = coerce(
        eval(Function.StepDefinition.get()), Function.StepDefinition->Sort,
        Function.ResultSort, isSigned(Function.ResultSort));
    Active.pop_back();
    Scope.resize(SavedSize);
    ScopeBase = SavedBase;
    if (!Value)
      return std::nullopt;
    Applications.emplace(Key, *Value);
    Evaluated.push_back({&Function, Args});
    // A model's application can be expensive to read: check the clock first.
    if (pastDeadline())
      return limit("the time limit was reached");
    std::optional<LogicValue> Claimed = Model.application(Function, Args);
    if (Claimed && !(*Claimed == *Value) && DisputeKeys.insert(Key).second)
      Disputes.push_back({&Function, Args});
    return Value;
  }

  std::optional<LogicValue> application(const LogicExpr *E) {
    auto It = Module.LogicFunctions.find(E->SpecCallee);
    if (It == Module.LogicFunctions.end())
      return fail("no declaration for " + E->SpecCallee);
    const LogicFunctionDecl &Function = It->second;
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
      if (!Value && Failure.empty())
        return fail("the model gives no value for an application of " +
                    Function.DisplayName);
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
    case Op::SeqUpdate: {
      const CertInt *I = integerAt(1);
      const CertInt *X = integerAt(2);
      if (!kindAt(0, VK::Seq) || !I || !X)
        break;
      std::vector<CertInt> S = *Operands[0].Elements;
      if (!I->isNegative() && *I < CertInt(static_cast<int64_t>(S.size())))
        S[static_cast<size_t>(I->bits(64).getZExtValue())] = *X;
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
    case LogicExpr::Or: {
      const bool Deciding = E->K == LogicExpr::Or;
      for (const auto &Child : E->Children) {
        std::optional<bool> Holds = truthOf(Child.get());
        if (!Holds)
          return std::nullopt;
        if (*Holds == Deciding)
          return LogicValue::boolean(Deciding);
      }
      return LogicValue::boolean(!Deciding);
    }
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
    if (++Steps > Limits.Steps)
      return limit("the evaluation step limit was reached");
    if ((Steps & 4095) == 0 && pastDeadline())
      return limit("the time limit was reached");
    if (Frames >= Limits.Frames)
      return limit("the evaluation nesting limit was reached");
    ++Frames;
    std::optional<LogicValue> Value = evalNode(E);
    --Frames;
    return Value;
  }

  const std::string &failure() const { return Failure; }
  bool limitInDefinition() const { return LimitInDefinition; }
  const LogicExpr *wideQuantifier() const { return Wide; }
  const LogicExpr *deepApplication() const { return Deep; }
  std::vector<SpecDispute> takeDisputes() { return std::move(Disputes); }
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
      return;
    }
    Evaluator Claimed(Module, Model, Limits, View::Model);
    std::optional<LogicValue> Satisfied = Claimed.eval(&Query);
    if (!Satisfied || Satisfied->K != LogicValue::Kind::Bool) {
      Result.Outcome = CertifyOutcome::Undetermined;
      Result.Detail =
          Satisfied ? "the query is not a formula" : Claimed.failure();
      Result.WideQuantifier = Claimed.wideQuantifier();
      return;
    }
    std::vector<SpecDispute> Disputes = Definitions.takeDisputes();
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
        if (Instance.Function->DefinitionFuel != 0 &&
            Seen.insert(Instance.key()).second)
          Instances.push_back(std::move(Instance));
    }
  };
  llvm::thread Worker(std::optional<unsigned>(CertifierStackBytes), Run);
  Worker.join();
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
  for (const SpecDispute &Dispute : Result.Disputes) {
    const LogicFunctionDecl &Function = *Dispute.Function;
    Disputed.insert(displayName(Function));
    DefinitionInstance Instance{&Function, Dispute.Arguments};
    if (!Given.insert(Instance.key()).second)
      continue;
    if (Function.DefinitionFuel == 0)
      HiddenGiven.insert(displayName(Function));
    else
      OnlyHidden = false;
    Decision.Instances.push_back(std::move(Instance));
  }
  if (Decision.Instances.empty()) {
    Decision.Reason = VerifyReason::InvalidBackendResult;
    Decision.Message = "the solver's model contradicts definition instances "
                       "it was given";
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
  Decision.Next = RefinementDecision::Action::Refine;
  return Decision;
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
