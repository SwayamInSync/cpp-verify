//===- CertifyTest.cpp - Counterexample certification ---------------------===//
//
// The certifier's canonical semantics against llvm::APInt and against every
// solver encoding, and its classification of solver models.
//
//===----------------------------------------------------------------------===//

#include "Backend/Certify.h"
#include "Backend/Presburger.h"
#include "Backend/VerifyBackend.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/Support/Program.h"
#include "gtest/gtest.h"
#include <cstdlib>
#include <functional>
#include <map>
#include <random>
#include <z3++.h>

using namespace clang::verify;
using llvm::APInt;

namespace {

using Expr = std::unique_ptr<LogicExpr>;

std::string decimal(const APInt &Value, bool Signed) {
  llvm::SmallString<64> Text;
  Value.toString(Text, 10, Signed);
  return std::string(Text);
}

Expr leaf(LogicExpr::Kind Kind, LogicSort Sort) {
  auto E = std::make_unique<LogicExpr>(Kind);
  E->Sort = Sort;
  return E;
}

Expr literal(llvm::StringRef Decimal, LogicSort Sort) {
  Expr E = leaf(LogicExpr::IntLit, Sort);
  E->IntVal = Decimal.str();
  return E;
}

Expr literal(const APInt &Value, LogicSort Sort) {
  return literal(decimal(Value, Sort.Signedness == LogicSignedness::Signed),
                 Sort);
}

LogicSort math() { return LogicSort::mathematicalInteger(64, true); }

Expr mathLiteral(int64_t Value) {
  return literal(std::to_string(Value), math());
}

Expr boolLiteral(bool Value) {
  return leaf(Value ? LogicExpr::True : LogicExpr::False,
              LogicSort::boolSort());
}

Expr variable(llvm::StringRef Name, LogicSort Sort) {
  Expr E = leaf(LogicExpr::Var, Sort);
  E->Name = Name.str();
  return E;
}

Expr node(LogicExpr::Kind Kind, LogicSort Sort, std::vector<Expr> Children) {
  Expr E = leaf(Kind, Sort);
  E->Children = std::move(Children);
  return E;
}

template <typename... Operands>
Expr node(LogicExpr::Kind Kind, LogicSort Sort, Operands... Children) {
  std::vector<Expr> List;
  (List.push_back(std::move(Children)), ...);
  return node(Kind, Sort, std::move(List));
}

Expr boolean(LogicExpr::Kind Kind, Expr L, Expr R) {
  return node(Kind, LogicSort::boolSort(), std::move(L), std::move(R));
}

Expr negation(Expr E) {
  return node(LogicExpr::Not, LogicSort::boolSort(), std::move(E));
}

Expr clone(const LogicExpr &E) {
  auto Copy = std::make_unique<LogicExpr>(E.K);
  Copy->Sort = E.Sort;
  Copy->IntVal = E.IntVal;
  Copy->BoolVal = E.BoolVal;
  Copy->Name = E.Name;
  Copy->Binder = E.Binder;
  Copy->OverflowOp = E.OverflowOp;
  Copy->SpecCallee = E.SpecCallee;
  for (const auto &Child : E.Children)
    Copy->Children.push_back(clone(*Child));
  return Copy;
}

Expr call(const LogicFunctionDecl &Function, std::vector<Expr> Args) {
  Expr E = node(LogicExpr::SpecCall, Function.ResultSort, std::move(Args));
  E->SpecCallee = Function.Identity;
  return E;
}

/// Free symbols and function interpretations fixed by a test.
class TableModel : public CandidateModel {
public:
  std::map<std::string, LogicValue> Constants;
  /// Keyed by function identity and argument keys.
  std::map<std::string, LogicValue> Applications;
  std::optional<LogicValue> DefaultApplication;
  std::map<std::string, bool> Valid;

  static std::string key(const std::string &Function,
                         const std::vector<LogicValue> &Arguments) {
    std::string Key = Function;
    for (const LogicValue &Argument : Arguments)
      Key += "|" + Argument.key();
    return Key;
  }

  std::optional<LogicValue> constant(const std::string &Name,
                                     const LogicSort &) override {
    auto It = Constants.find(Name);
    if (It == Constants.end())
      return std::nullopt;
    return It->second;
  }

  std::optional<bool> validPointer(const CertInt &Address) override {
    auto It = Valid.find(Address.toDecimal());
    if (It == Valid.end())
      return false;
    return It->second;
  }

  std::optional<LogicValue>
  application(const LogicFunctionDecl &Function,
              const std::vector<LogicValue> &Arguments) override {
    auto It = Applications.find(key(Function.Identity, Arguments));
    if (It != Applications.end())
      return It->second;
    return DefaultApplication;
  }
};

LogicValue integerValue(int64_t Value) {
  return LogicValue::integer(CertInt(Value));
}

CertifyOutcome certifyGround(const LogicExpr &Query,
                             const ObligationModule &Module = {}) {
  TableModel Model;
  return certifyCounterexample(Module, Query, Model).Outcome;
}

// --- CertInt
// ------------------------------------------------------------------

APInt wideOf(const CertInt &Value) { return Value.bits(512); }

CertInt fromWide(const APInt &Value) { return CertInt::fromBits(Value, true); }

TEST(CertifyTest, IntegersMatchWideAPInt) {
  std::mt19937_64 Random(7);
  auto sample = [&]() {
    const unsigned Width = 1 + Random() % 200;
    llvm::SmallVector<uint64_t, 4> Words((Width + 63) / 64);
    for (uint64_t &Word : Words)
      Word = Random();
    return CertInt::fromBits(APInt(Width, Words), Random() % 2 == 0);
  };
  for (unsigned I = 0; I != 4000; ++I) {
    const CertInt A = I < 16 ? CertInt(static_cast<int64_t>(I) - 8) : sample();
    const CertInt B = sample();
    const APInt WA = wideOf(A);
    const APInt WB = wideOf(B);
    EXPECT_EQ(A + B, fromWide(WA + WB));
    EXPECT_EQ(A - B, fromWide(WA - WB));
    EXPECT_EQ(A * B, fromWide(WA * WB));
    EXPECT_EQ(-A, fromWide(-WA));
    EXPECT_EQ(A.compare(B) < 0, WA.slt(WB));
    EXPECT_EQ(A == B, WA == WB);
    EXPECT_EQ(CertInt::fromDecimal(A.toDecimal()), A);
    EXPECT_EQ(A.toDecimal(), decimal(WA, true));
    if (B.isZero())
      continue;
    EXPECT_EQ(A.truncDiv(B), fromWide(WA.sdiv(WB)));
    APInt Quotient = WA.sdiv(WB);
    if (!WA.srem(WB).isZero() && WA.isNegative() != WB.isNegative())
      Quotient -= 1;
    EXPECT_EQ(A.floorDiv(B), fromWide(Quotient));
  }
  EXPECT_FALSE(CertInt::fromDecimal(""));
  EXPECT_FALSE(CertInt::fromDecimal("-"));
  EXPECT_FALSE(CertInt::fromDecimal("1a"));
  EXPECT_EQ(CertInt::powerOfTwo(100).toDecimal(),
            "1267650600228229401496703205376");
}

// --- Machine operators against APInt
// ------------------------------------------

enum class Binary {
  Add,
  Sub,
  Mul,
  Div,
  Rem,
  And,
  Or,
  Xor,
  Shl,
  Shr,
  Lt,
  Le,
  Gt,
  Ge,
  Eq,
  Ne
};

const Binary AllBinary[] = {Binary::Add, Binary::Sub, Binary::Mul, Binary::Div,
                            Binary::Rem, Binary::And, Binary::Or,  Binary::Xor,
                            Binary::Shl, Binary::Shr, Binary::Lt,  Binary::Le,
                            Binary::Gt,  Binary::Ge,  Binary::Eq,  Binary::Ne};

LogicExpr::Kind kindOf(Binary Op) {
  static const LogicExpr::Kind Kinds[] = {
      LogicExpr::Add, LogicExpr::Sub,    LogicExpr::Mul,   LogicExpr::Div,
      LogicExpr::Rem, LogicExpr::BitAnd, LogicExpr::BitOr, LogicExpr::BitXor,
      LogicExpr::Shl, LogicExpr::Shr,    LogicExpr::Lt,    LogicExpr::Le,
      LogicExpr::Gt,  LogicExpr::Ge,     LogicExpr::Eq,    LogicExpr::Ne};
  return Kinds[static_cast<unsigned>(Op)];
}

bool isComparison(Binary Op) { return Op >= Binary::Lt; }

/// SMT-LIB bit-vector semantics, the reference for both machine encodings.
APInt reference(Binary Op, const APInt &A, const APInt &B, bool Signed) {
  const unsigned W = A.getBitWidth();
  auto wide = [&](const APInt &V) {
    return Signed ? V.sext(W + 1) : V.zext(W + 1);
  };
  auto truth = [](bool Value) { return APInt(1, Value ? 1 : 0); };
  switch (Op) {
  case Binary::Add:
    return A + B;
  case Binary::Sub:
    return A - B;
  case Binary::Mul:
    return A * B;
  case Binary::Div:
    if (B.isZero())
      return Signed && A.isNegative() ? APInt(W, 1) : APInt::getAllOnes(W);
    return (Signed ? wide(A).sdiv(wide(B)) : A.udiv(B)).trunc(W);
  case Binary::Rem:
    if (B.isZero())
      return A;
    return (Signed ? wide(A).srem(wide(B)) : A.urem(B)).trunc(W);
  case Binary::And:
    return A & B;
  case Binary::Or:
    return A | B;
  case Binary::Xor:
    return A ^ B;
  case Binary::Shl:
    return B.uge(W) ? APInt(W, 0)
                    : A.shl(static_cast<unsigned>(B.getZExtValue()));
  case Binary::Shr:
    if (B.uge(W))
      return Signed && A.isNegative() ? APInt::getAllOnes(W) : APInt(W, 0);
    return Signed ? A.ashr(static_cast<unsigned>(B.getZExtValue()))
                  : A.lshr(static_cast<unsigned>(B.getZExtValue()));
  case Binary::Lt:
    return truth(Signed ? A.slt(B) : A.ult(B));
  case Binary::Le:
    return truth(Signed ? A.sle(B) : A.ule(B));
  case Binary::Gt:
    return truth(Signed ? A.sgt(B) : A.ugt(B));
  case Binary::Ge:
    return truth(Signed ? A.sge(B) : A.uge(B));
  case Binary::Eq:
    return truth(A == B);
  case Binary::Ne:
    return truth(A != B);
  }
  llvm_unreachable("unknown operator");
}

std::vector<APInt> operandValues(unsigned W, std::mt19937_64 &Random) {
  std::vector<APInt> Values;
  if (W <= 4) {
    for (uint64_t V = 0; V != (1ULL << W); ++V)
      Values.push_back(APInt(W, V));
    return Values;
  }
  for (const APInt &V :
       {APInt(W, 0), APInt(W, 1), APInt(W, 2), APInt::getAllOnes(W),
        APInt::getSignedMinValue(W), APInt::getSignedMaxValue(W),
        APInt(W, W - 1), APInt(W, W)})
    Values.push_back(V);
  for (unsigned I = 0; I != 5; ++I) {
    llvm::SmallVector<uint64_t, 4> Words((W + 63) / 64);
    for (uint64_t &Word : Words)
      Word = Random();
    Values.push_back(APInt(W, Words));
  }
  return Values;
}

const unsigned Widths[] = {1, 2, 3, 4, 7, 8, 16, 32, 33, 64, 128};

/// `Applied == Expected` holds; its corrupted twin is refuted in both views.
void expectGround(Expr Applied, Expr Expected, Expr Corrupted,
                  const std::string &What) {
  Expr Holds = boolean(LogicExpr::Eq, clone(*Applied), std::move(Expected));
  Expr Fails = boolean(LogicExpr::Eq, std::move(Applied), std::move(Corrupted));
  EXPECT_EQ(certifyGround(*Holds), CertifyOutcome::Certified) << What;
  EXPECT_EQ(certifyGround(*Fails), CertifyOutcome::Inconsistent) << What;
}

TEST(CertifyTest, MachineBinaryOperatorsMatchAPInt) {
  std::mt19937_64 Random(11);
  for (unsigned W : Widths)
    for (bool Signed : {true, false})
      for (Binary Op : AllBinary)
        for (bool AmountSigned : {true, false}) {
          if (AmountSigned != Signed && Op != Binary::Shl && Op != Binary::Shr)
            continue;
          const LogicSort Sort = LogicSort::bitVector(W, Signed);
          const LogicSort Right = LogicSort::bitVector(W, AmountSigned);
          const std::vector<APInt> Values = operandValues(W, Random);
          for (const APInt &A : Values)
            for (const APInt &B : Values) {
              const APInt Expected = reference(Op, A, B, Signed);
              const std::string What =
                  "op " + std::to_string(static_cast<unsigned>(Op)) + " w" +
                  std::to_string(W) + (Signed ? "s" : "u") + " " +
                  decimal(A, false) + ", " + decimal(B, false);
              Expr Applied = node(
                  kindOf(Op), isComparison(Op) ? LogicSort::boolSort() : Sort,
                  literal(A, Sort), literal(B, Right));
              if (isComparison(Op))
                expectGround(std::move(Applied), boolLiteral(Expected.isOne()),
                             boolLiteral(!Expected.isOne()), What);
              else
                expectGround(std::move(Applied), literal(Expected, Sort),
                             literal(Expected + 1, Sort), What);
            }
        }
}

TEST(CertifyTest, MachineUnaryOperatorsAndConversionsMatchAPInt) {
  std::mt19937_64 Random(13);
  for (unsigned W : Widths)
    for (bool Signed : {true, false}) {
      const LogicSort Sort = LogicSort::bitVector(W, Signed);
      for (const APInt &A : operandValues(W, Random)) {
        const std::string What = "w" + std::to_string(W) +
                                 (Signed ? "s " : "u ") + decimal(A, false);
        expectGround(node(LogicExpr::Neg, Sort, literal(A, Sort)),
                     literal(-A, Sort), literal(-A + 1, Sort), "neg " + What);
        expectGround(node(LogicExpr::BitNot, Sort, literal(A, Sort)),
                     literal(~A, Sort), literal(~A + 1, Sort), "not " + What);
        const APInt Value = Signed ? A.sext(W + 1) : A.zext(W + 1);
        expectGround(node(LogicExpr::BvToInt, math(), literal(A, Sort)),
                     literal(decimal(Value, true), math()),
                     literal(decimal(Value + 1, true), math()),
                     "bv2int " + What);
        for (unsigned To : {1U, 5U, 8U, 32U, 64U, 130U})
          for (bool ToSigned : {true, false}) {
            const LogicSort Target = LogicSort::bitVector(To, ToSigned);
            const APInt Resized =
                Signed ? A.sextOrTrunc(To) : A.zextOrTrunc(To);
            expectGround(node(LogicExpr::BvResize, Target, literal(A, Sort)),
                         literal(Resized, Target), literal(Resized + 1, Target),
                         "resize " + What + " to " + std::to_string(To));
            // A mathematical value reduces modulo 2^To.
            const APInt Wide = Value.sext(W + 70) * 12345;
            expectGround(node(LogicExpr::IntToBv, Target,
                              literal(decimal(Wide, true), math())),
                         literal(Wide.sextOrTrunc(To), Target),
                         literal(Wide.sextOrTrunc(To) + 1, Target),
                         "int2bv " + What + " to " + std::to_string(To));
          }
      }
    }
}

TEST(CertifyTest, OverflowPredicatesMatchAPInt) {
  std::mt19937_64 Random(17);
  for (unsigned W : Widths)
    for (bool LeftSigned : {true, false})
      for (bool RightSigned : {true, false}) {
        const LogicSort Left = LogicSort::bitVector(W, LeftSigned);
        const LogicSort Right = LogicSort::bitVector(W, RightSigned);
        const std::vector<APInt> Values = operandValues(W, Random);
        for (const APInt &A : Values)
          for (const APInt &B : Values) {
            // Operands are read as signed w-bit values.
            const APInt SA = A.sext(2 * W + 2);
            const APInt SB = B.sext(2 * W + 2);
            auto fits = [&](const APInt &Exact) {
              return Exact.sge(APInt::getSignedMinValue(W).sext(2 * W + 2)) &&
                     Exact.sle(APInt::getSignedMaxValue(W).sext(2 * W + 2));
            };
            const std::pair<LogicOverflowOp, bool> Cases[] = {
                {LogicOverflowOp::Add, fits(SA + SB)},
                {LogicOverflowOp::Sub, fits(SA - SB)},
                {LogicOverflowOp::Mul, fits(SA * SB)},
                {LogicOverflowOp::SignedDiv,
                 !(A.isMinSignedValue() && B.isAllOnes())},
                {LogicOverflowOp::Neg, fits(-SA)}};
            for (const auto &[Op, Holds] : Cases) {
              std::vector<Expr> Operands;
              Operands.push_back(literal(A, Left));
              if (Op != LogicOverflowOp::Neg)
                Operands.push_back(literal(B, Right));
              Expr Check = node(LogicExpr::NoOverflow, LogicSort::boolSort(),
                                std::move(Operands));
              Check->OverflowOp = Op;
              expectGround(std::move(Check), boolLiteral(Holds),
                           boolLiteral(!Holds),
                           "overflow " + std::to_string(static_cast<int>(Op)) +
                               " w" + std::to_string(W));
            }
          }
      }
}

TEST(CertifyTest, MathematicalDivisionTruncates) {
  std::mt19937_64 Random(19);
  for (unsigned I = 0; I != 2000; ++I) {
    const int64_t A = static_cast<int64_t>(Random()) >> (Random() % 60);
    const int64_t B =
        I % 10 == 0 ? 0 : static_cast<int64_t>(Random()) >> (Random() % 63);
    const __int128 Q = B == 0 ? 0 : static_cast<__int128>(A) / B;
    const __int128 R = B == 0 ? A : static_cast<__int128>(A) % B;
    auto text = [](__int128 V) {
      return decimal(APInt(128, {static_cast<uint64_t>(V),
                                 static_cast<uint64_t>(V >> 64)}),
                     true);
    };
    expectGround(node(LogicExpr::Div, math(), mathLiteral(A), mathLiteral(B)),
                 literal(text(Q), math()), literal(text(Q + 1), math()), "div");
    expectGround(node(LogicExpr::Rem, math(), mathLiteral(A), mathLiteral(B)),
                 literal(text(R), math()), literal(text(R + 1), math()), "rem");
  }
}

// --- Heaps, quantifiers, and free symbols
// -------------------------------------

LogicValue heapOf(std::map<int64_t, int64_t> Cells, int64_t Default) {
  HeapValue Heap;
  Heap.Default = CertInt(Default);
  for (const auto &[Address, Cell] : Cells)
    Heap.set(CertInt(Address), CertInt(Cell));
  return LogicValue::heap(std::move(Heap));
}

TEST(CertifyTest, HeapsReadCellsAndRelateStores) {
  TableModel Model;
  Model.Constants["h0"] = heapOf({{8, 5}, {16, 4294967295}}, 0);
  Model.Constants["h1"] = heapOf({{8, 5}, {16, 4294967295}, {24, 7}}, 0);
  Model.Constants["h2"] = heapOf({{8, 5}, {16, 4294967295}, {24, 0}}, 0);
  const LogicSort I32 = LogicSort::bitVector(32, true);
  auto load = [&](const char *Heap, int64_t Address, LogicSort Sort) {
    return node(LogicExpr::Select, Sort, variable(Heap, LogicSort::heap()),
                literal(std::to_string(Address), LogicSort::pointer()));
  };
  auto store = [&](const char *Before, int64_t Address, Expr Value,
                   const char *After) {
    return node(LogicExpr::Store, LogicSort::boolSort(),
                variable(Before, LogicSort::heap()),
                literal(std::to_string(Address), LogicSort::pointer()),
                std::move(Value), variable(After, LogicSort::heap()));
  };
  ObligationModule Module;
  auto outcome = [&](Expr Query) {
    return certifyCounterexample(Module, *Query, Model).Outcome;
  };
  // A cell holds the unsigned pattern; a typed load reads its low bits.
  EXPECT_EQ(
      outcome(boolean(LogicExpr::Eq, load("h0", 16, I32), literal("-1", I32))),
      CertifyOutcome::Certified);
  EXPECT_EQ(outcome(boolean(LogicExpr::Eq, load("h0", 16, LogicSort::pointer()),
                            literal("4294967295", LogicSort::pointer()))),
            CertifyOutcome::Certified);
  EXPECT_EQ(outcome(load("h0", 8, LogicSort::boolSort())),
            CertifyOutcome::Certified);
  EXPECT_EQ(outcome(store("h0", 24, literal("7", I32), "h1")),
            CertifyOutcome::Certified);
  EXPECT_EQ(outcome(store("h0", 24, literal("8", I32), "h1")),
            CertifyOutcome::Inconsistent);
  // Storing the default value leaves the same array.
  EXPECT_EQ(outcome(store("h0", 24, literal("0", I32), "h0")),
            CertifyOutcome::Certified);
  EXPECT_EQ(outcome(boolean(LogicExpr::Eq, variable("h0", LogicSort::heap()),
                            variable("h2", LogicSort::heap()))),
            CertifyOutcome::Certified);
  EXPECT_EQ(outcome(store("h0", 16, literal("-1", I32), "h0")),
            CertifyOutcome::Certified);
}

TEST(CertifyTest, HeapFramesCompareWholeSegments) {
  TableModel Model;
  Model.Constants["h0"] = heapOf({{8, 5}, {16, 9}}, 0);
  // A range [100, 140) set to 3, and the cell at 8 changed.
  HeapValue Range = *heapOf({{8, 6}, {16, 9}}, 0).Heap;
  Range.setRange(CertInt(100), CertInt(140), CertInt(3));
  Model.Constants["h1"] = LogicValue::heap(Range);
  // Every cell from 1000 on changed.
  HeapValue Tail = *heapOf({{8, 5}, {16, 9}}, 0).Heap;
  Tail.setRange(CertInt(1000), CertInt(1001), CertInt(1));
  Tail.Breaks.erase(CertInt(1001));
  Model.Constants["h2"] = LogicValue::heap(Tail);
  // Every cell changed.
  Model.Constants["h3"] = heapOf({{8, 5}, {16, 9}}, 7);
  auto frame = [&](const char *Before, const char *After,
                   std::vector<std::pair<int64_t, int64_t>> Regions) {
    std::vector<Expr> Children;
    Children.push_back(variable(Before, LogicSort::heap()));
    Children.push_back(variable(After, LogicSort::heap()));
    for (const auto &[Lo, Hi] : Regions) {
      Children.push_back(literal(std::to_string(Lo), LogicSort::pointer()));
      Children.push_back(literal(std::to_string(Hi), LogicSort::pointer()));
    }
    return node(LogicExpr::HeapFrame, LogicSort::boolSort(),
                std::move(Children));
  };
  ObligationModule Module;
  auto outcome = [&](Expr Query) {
    return certifyCounterexample(Module, *Query, Model).Outcome;
  };
  EXPECT_EQ(outcome(frame("h0", "h0", {})), CertifyOutcome::Certified);
  EXPECT_EQ(outcome(frame("h0", "h1", {{8, 9}, {100, 140}})),
            CertifyOutcome::Certified);
  // Adjacent regions cover a segment together.
  EXPECT_EQ(outcome(frame("h0", "h1", {{120, 140}, {8, 9}, {100, 120}})),
            CertifyOutcome::Certified);
  EXPECT_EQ(outcome(frame("h0", "h1", {{8, 9}, {100, 139}})),
            CertifyOutcome::Inconsistent);
  EXPECT_EQ(outcome(frame("h0", "h1", {{100, 140}})),
            CertifyOutcome::Inconsistent);
  // An empty region covers nothing.
  EXPECT_EQ(outcome(frame("h0", "h1", {{9, 8}, {100, 140}})),
            CertifyOutcome::Inconsistent);
  // A change without end, or everywhere, escapes every finite region.
  EXPECT_EQ(outcome(frame("h0", "h2", {{1000, 1000000}})),
            CertifyOutcome::Inconsistent);
  EXPECT_EQ(outcome(frame("h0", "h3", {{-1000000, 1000000}})),
            CertifyOutcome::Inconsistent);
  EXPECT_EQ(outcome(negation(frame("h0", "h1", {{100, 140}}))),
            CertifyOutcome::Certified);
}

TEST(CertifyTest, CollectionsReadAndDisplay) {
  EXPECT_EQ(formatLogicValue(LogicValue::sequence(
                {CertInt(1), CertInt(-2), CertInt(3)})),
            "[1, -2, 3]");
  EXPECT_EQ(formatLogicValue(LogicValue::sequence({})), "[]");
  HeapValue Members;
  Members.set(CertInt(1), CertInt(1));
  Members.setRange(CertInt(3), CertInt(6), CertInt(1));
  EXPECT_EQ(formatLogicValue(LogicValue::set(Members)), "{1, 3..5}");
  HeapValue Everything;
  Everything.Default = CertInt(1);
  EXPECT_EQ(formatLogicValue(LogicValue::set(Everything)), "{..}");
  HeapValue Counts;
  Counts.set(CertInt(2), CertInt(3));
  EXPECT_EQ(formatLogicValue(LogicValue::multiset(Counts)), "{2: 3}");
  HeapValue Domain, Values;
  Domain.set(CertInt(1), CertInt(1));
  Domain.Breaks[CertInt(4)] = CertInt(1);
  Values.set(CertInt(1), CertInt(7));
  Values.Breaks[CertInt(4)] = CertInt(2);
  EXPECT_EQ(formatLogicValue(LogicValue::map(Domain, Values)),
            "{1 -> 7, 4.. -> 2}");

  // Over all integers, a sequence read is decided at its indices and beyond.
  TableModel Model;
  Model.Constants["s"] =
      LogicValue::sequence({CertInt(3), CertInt(-1), CertInt(2)});
  ObligationModule Module;
  auto everyElement = [](LogicExpr::Kind Compare, int64_t Bound) {
    Expr Read = node(LogicExpr::Collection, math(),
                     variable("s", LogicSort::collection(LogicSortKind::Seq)),
                     variable("k", math()));
    Read->CollectionOp = LogicCollectionOp::SeqIndex;
    Expr Q = node(LogicExpr::Forall, LogicSort::boolSort(),
                  boolean(Compare, std::move(Read), mathLiteral(Bound)));
    Q->Binder = "k";
    return Q;
  };
  EXPECT_EQ(certifyCounterexample(Module, *negation(everyElement(
                                              LogicExpr::Ge, 0)),
                                  Model)
                .Outcome,
            CertifyOutcome::Certified);
  EXPECT_EQ(certifyCounterexample(Module, *negation(everyElement(
                                              LogicExpr::Le, 3)),
                                  Model)
                .Outcome,
            CertifyOutcome::Inconsistent);
}

TEST(CertifyTest, QuantifiersExpandTheirRange) {
  TableModel Model;
  Model.Constants["n"] = integerValue(50);
  ObligationModule Module;
  auto square = [](const char *Binder, Expr Bound, LogicExpr::Kind Kind,
                   Expr Body) {
    Expr Q = node(Kind, LogicSort::boolSort(), mathLiteral(0), std::move(Bound),
                  std::move(Body));
    Q->Binder = Binder;
    return Q;
  };
  auto i = [] { return variable("i", math()); };
  Expr AllNonNegative =
      square("i", variable("n", math()), LogicExpr::Forall,
             boolean(LogicExpr::Ge, node(LogicExpr::Mul, math(), i(), i()),
                     mathLiteral(0)));
  EXPECT_EQ(certifyCounterexample(Module, *AllNonNegative, Model).Outcome,
            CertifyOutcome::Certified);
  Expr SomeSquareIs49 =
      square("i", variable("n", math()), LogicExpr::Exists,
             boolean(LogicExpr::Eq, node(LogicExpr::Mul, math(), i(), i()),
                     mathLiteral(49)));
  EXPECT_EQ(certifyCounterexample(Module, *SomeSquareIs49, Model).Outcome,
            CertifyOutcome::Certified);
  Expr SomeSquareIs50 =
      square("i", variable("n", math()), LogicExpr::Exists,
             boolean(LogicExpr::Eq, node(LogicExpr::Mul, math(), i(), i()),
                     mathLiteral(50)));
  EXPECT_EQ(certifyCounterexample(Module, *SomeSquareIs50, Model).Outcome,
            CertifyOutcome::Inconsistent);
  // A range too wide to expand is still decided by an instance near an end.
  Model.Constants["n"] = integerValue(int64_t(1) << 40);
  EXPECT_EQ(certifyCounterexample(Module, *SomeSquareIs49, Model).Outcome,
            CertifyOutcome::Certified);
  Expr LastIsExcluded =
      square("i", variable("n", math()), LogicExpr::Forall,
             boolean(LogicExpr::Ne, i(),
                     node(LogicExpr::Sub, math(), variable("n", math()),
                          mathLiteral(1))));
  EXPECT_EQ(certifyCounterexample(Module, *LastIsExcluded, Model).Outcome,
            CertifyOutcome::Inconsistent);
  // A polynomial body is decided between the roots of its comparisons.
  EXPECT_EQ(certifyCounterexample(Module, *AllNonNegative, Model).Outcome,
            CertifyOutcome::Certified);
  // Otherwise it cannot be checked, and the adapter may narrow that range.
  Expr ThirdsNonNegative =
      square("i", variable("n", math()), LogicExpr::Forall,
             boolean(LogicExpr::Ge,
                     node(LogicExpr::Div, math(), i(), mathLiteral(3)),
                     mathLiteral(0)));
  CertifyResult Huge = certifyCounterexample(Module, *ThirdsNonNegative, Model);
  EXPECT_EQ(Huge.Outcome, CertifyOutcome::Undetermined);
  EXPECT_FALSE(Huge.DefinitionTooDeep);
  EXPECT_EQ(Huge.WideQuantifier, ThirdsNonNegative.get());
  RefinementDecision Decision = DefinitionRefinement(Module).next(Huge);
  EXPECT_EQ(Decision.Reason, VerifyReason::UncheckedCounterexample);
  // A quantifier under another binder is not one the adapter can narrow.
  Expr Nested =
      square("j", mathLiteral(1), LogicExpr::Forall, clone(*ThirdsNonNegative));
  CertifyResult Inner = certifyCounterexample(Module, *Nested, Model);
  EXPECT_EQ(Inner.Outcome, CertifyOutcome::Undetermined);
  EXPECT_EQ(Inner.WideQuantifier, nullptr);
}

TEST(CertifyTest, WideRangesOverLoadsMatchExpansion) {
  // A body that depends on the binder only through load addresses and affine
  // comparisons is checked at the values hitting explicit cells or comparison
  // roots plus one value between each two; that must agree with expanding
  // every value.
  std::mt19937_64 Random(31);
  auto pick = [&](int64_t Low, int64_t High) {
    return Low + static_cast<int64_t>(Random() % (High - Low + 1));
  };
  const LogicSort I32 = LogicSort::bitVector(32, true);
  ObligationModule Module;
  unsigned Decided[2] = {0, 0};
  for (unsigned Case = 0; Case != 3000; ++Case) {
    TableModel Model;
    for (const char *Name : {"h", "g"}) {
      std::map<int64_t, int64_t> Cells;
      for (int64_t I = pick(0, 12); I > 0; --I)
        Cells[pick(-50, 900)] = pick(-3, 3);
      Model.Constants[Name] = heapOf(Cells, pick(-1, 1));
    }
    auto address = [&] {
      Expr Scaled = node(LogicExpr::Mul, math(), mathLiteral(pick(-3, 4)),
                         variable("i", math()));
      if (pick(0, 3) == 0)
        Scaled = node(LogicExpr::Neg, math(), std::move(Scaled));
      return node(pick(0, 1) ? LogicExpr::Add : LogicExpr::Sub,
                  LogicSort::pointer(),
                  literal(std::to_string(pick(-20, 60)), LogicSort::pointer()),
                  std::move(Scaled));
    };
    auto load = [&](const char *Heap) {
      return node(LogicExpr::Select, I32, variable(Heap, LogicSort::heap()),
                  address());
    };
    static const LogicExpr::Kind Comparisons[] = {LogicExpr::Lt, LogicExpr::Le,
                                                  LogicExpr::Gt, LogicExpr::Ge,
                                                  LogicExpr::Eq, LogicExpr::Ne};
    auto affine = [&] {
      return node(LogicExpr::Add, math(),
                  node(LogicExpr::Mul, math(), mathLiteral(pick(-3, 3)),
                       variable("i", math())),
                  mathLiteral(pick(-60, 60)));
    };
    auto power = [&](unsigned Degree) {
      Expr Term = variable("i", math());
      for (unsigned I = 1; I < Degree; ++I)
        Term = node(LogicExpr::Mul, math(), std::move(Term),
                    variable("i", math()));
      return Term;
    };
    // A polynomial of degree 2 or 3 with integer coefficients.
    auto polynomial = [&](unsigned Degree) {
      Expr Sum = mathLiteral(pick(-400, 400));
      for (unsigned D = 1; D <= Degree; ++D)
        Sum = node(LogicExpr::Add, math(), std::move(Sum),
                   node(LogicExpr::Mul, math(),
                        mathLiteral(D == Degree ? pick(-3, 3) : pick(-60, 60)),
                        power(D)));
      return Sum;
    };
    const LogicSort I8 = LogicSort::bitVector(8, pick(0, 1) != 0);
    const LogicSort I16 = LogicSort::bitVector(16, pick(0, 1) != 0);
    Expr Body;
    // a * i * i + b * i + c in machine arithmetic of sort S.
    auto machineQuadratic = [&](LogicSort S) {
      // Converted directly, or through a narrower sort and widened.
      const bool Widened = pick(0, 1) != 0;
      auto converted = [&] {
        if (!Widened)
          return node(LogicExpr::IntToBv, S, variable("i", math()));
        const LogicSort Narrow = LogicSort::bitVector(S.BitWidth / 2, true);
        return node(LogicExpr::BvResize, S,
                    node(LogicExpr::IntToBv, Narrow, variable("i", math())));
      };
      Expr Square = node(LogicExpr::Mul, S, converted(), converted());
      Expr Scaled = node(LogicExpr::Mul, S,
                         literal(std::to_string(pick(-3, 3)), S),
                         std::move(Square));
      Expr Linear = node(LogicExpr::Mul, S,
                         literal(std::to_string(pick(-60, 60)), S), converted());
      return node(LogicExpr::Add, S,
                  node(LogicExpr::Add, S, std::move(Scaled), std::move(Linear)),
                  literal(std::to_string(pick(-400, 400)), S));
    };
    const int64_t Shape = pick(0, 11);
    switch (Shape) {
    case 0:
      Body = boolean(Comparisons[pick(0, 5)], load("h"),
                     literal(std::to_string(pick(-2, 2)), I32));
      break;
    case 1:
      Body = boolean(Comparisons[pick(0, 5)], load("h"), load("g"));
      break;
    case 2:
      Body = boolean(pick(0, 1) ? LogicExpr::And : LogicExpr::Or,
                     boolean(Comparisons[pick(0, 5)], load("h"),
                             literal(std::to_string(pick(-2, 2)), I32)),
                     boolean(Comparisons[pick(0, 5)], load("g"), load("h")));
      break;
    case 3:
      // An affine comparison on the binder changes only at its root.
      Body = boolean(pick(0, 1) ? LogicExpr::And : LogicExpr::Or,
                     boolean(Comparisons[pick(0, 5)], affine(),
                             mathLiteral(pick(-40, 40))),
                     boolean(Comparisons[pick(0, 5)], load("h"),
                             literal(std::to_string(pick(-2, 2)), I32)));
      break;
    case 4:
      Body = boolean(Comparisons[pick(0, 5)], affine(), affine());
      break;
    case 5:
      // A machine conversion of an affine term qualifies only where it does
      // not wrap, which an 8-bit sort often does over these ranges.
      Body = boolean(pick(0, 1) ? LogicExpr::And : LogicExpr::Or,
                     boolean(Comparisons[pick(0, 5)],
                             node(LogicExpr::IntToBv, I8, affine()),
                             literal(std::to_string(pick(0, 9)), I8)),
                     boolean(Comparisons[pick(0, 5)], load("g"),
                             literal(std::to_string(pick(-2, 2)), I32)));
      break;
    case 6:
      // Depends on the binder directly: never eligible for the shortcut.
      Body = boolean(Comparisons[pick(0, 5)],
                     node(LogicExpr::Add, I32, load("h"),
                          node(LogicExpr::IntToBv, I32, variable("i", math()))),
                     literal(std::to_string(pick(-2, 300)), I32));
      break;
    case 7:
      // A polynomial comparison changes only at its real roots.
      Body = boolean(pick(0, 1) ? LogicExpr::And : LogicExpr::Or,
                     boolean(Comparisons[pick(0, 5)], polynomial(2),
                             polynomial(pick(1, 2))),
                     boolean(Comparisons[pick(0, 5)], load("h"),
                             literal(std::to_string(pick(-2, 2)), I32)));
      break;
    case 8:
      Body = boolean(Comparisons[pick(0, 5)], polynomial(3),
                     mathLiteral(pick(-5000, 5000)));
      break;
    case 9:
      // A converted polynomial qualifies only where it does not wrap.
      Body = boolean(Comparisons[pick(0, 5)],
                     node(LogicExpr::IntToBv, I16, polynomial(2)),
                     literal(std::to_string(pick(0, 300)), I16));
      break;
    case 10:
      // Machine arithmetic that stays in its sort is exact.
      Body = boolean(Comparisons[pick(0, 5)], machineQuadratic(I32),
                     literal(std::to_string(pick(-3000, 3000)), I32));
      break;
    default:
      // ... and in a 16-bit sort it often wraps, which needs expansion.
      Body = boolean(Comparisons[pick(0, 5)],
                     machineQuadratic(LogicSort::bitVector(16, true)),
                     literal(std::to_string(pick(-3000, 3000)),
                             LogicSort::bitVector(16, true)));
      break;
    }
    const int64_t Low = pick(-40, 40);
    Expr Quantified = node(pick(0, 1) ? LogicExpr::Forall : LogicExpr::Exists,
                           LogicSort::boolSort(), mathLiteral(Low),
                           mathLiteral(Low + pick(0, 700)), std::move(Body));
    Quantified->Binder = "i";
    CertifyLimits Shortcut;
    Shortcut.DirectExpansion = 0;
    CertifyLimits Expanded;
    Expanded.DirectExpansion = 1000000;
    std::optional<LogicValue> Fast =
        evaluateTerm(Module, *Quantified, Model, Shortcut);
    std::optional<LogicValue> Slow =
        evaluateTerm(Module, *Quantified, Model, Expanded);
    ASSERT_TRUE(Fast && Slow) << "case " << Case;
    EXPECT_EQ(Fast->Truth, Slow->Truth) << "case " << Case;
    ++Decided[Slow->Truth];
    if (Shape < 5 || Shape == 7 || Shape == 8 || Shape == 10) {
      // These shapes never need expansion.
      CertifyLimits NoExpansion = Shortcut;
      NoExpansion.QuantifierInstances = 0;
      NoExpansion.QuantifierProbe = 0;
      EXPECT_TRUE(evaluateTerm(Module, *Quantified, Model, NoExpansion))
          << "case " << Case;
    }
  }
  // Both answers occur, so the comparison is not vacuous.
  EXPECT_GT(Decided[0], 300U);
  EXPECT_GT(Decided[1], 300U);
}

TEST(CertifyTest, PolynomialComparisonsOverHugeRanges) {
  // Ranges far too wide to expand, decided exactly at the roots.
  ObligationModule Module;
  TableModel Model;
  auto i = [] { return variable("i", math()); };
  auto square = [&](Expr E) {
    Expr Copy = clone(*E);
    return node(LogicExpr::Mul, math(), std::move(E), std::move(Copy));
  };
  auto quantified = [&](LogicExpr::Kind K, int64_t Low, int64_t High,
                        Expr Body) {
    Expr Q = node(K, LogicSort::boolSort(), mathLiteral(Low), mathLiteral(High),
                  std::move(Body));
    Q->Binder = "i";
    return Q;
  };
  CertifyLimits Limits;
  Limits.QuantifierInstances = 0;
  Limits.QuantifierProbe = 0;
  auto truth = [&](const Expr &Q) -> std::optional<bool> {
    std::optional<LogicValue> V = evaluateTerm(Module, *Q, Model, Limits);
    if (!V)
      return std::nullopt;
    return V->Truth;
  };
  const int64_t Wide = 1000000000;
  // (i - 1000000)^2 + 1 > 0 everywhere: a double root's neighbourhood.
  EXPECT_EQ(truth(quantified(
                LogicExpr::Forall, -Wide, Wide,
                boolean(LogicExpr::Gt,
                        node(LogicExpr::Add, math(),
                             square(node(LogicExpr::Sub, math(), i(),
                                         mathLiteral(1000000))),
                             mathLiteral(1)),
                        mathLiteral(0)))),
            std::optional<bool>(true));
  // ... but (i - 1000000)^2 > 0 fails at the root.
  EXPECT_EQ(truth(quantified(
                LogicExpr::Forall, -Wide, Wide,
                boolean(LogicExpr::Gt,
                        square(node(LogicExpr::Sub, math(), i(),
                                    mathLiteral(1000000))),
                        mathLiteral(0)))),
            std::optional<bool>(false));
  // i * i == 999999 * 999999 has a witness; i * i == 2 has none.
  EXPECT_EQ(truth(quantified(LogicExpr::Exists, 0, Wide,
                             boolean(LogicExpr::Eq, square(i()),
                                     mathLiteral(999999LL * 999999LL)))),
            std::optional<bool>(true));
  EXPECT_EQ(truth(quantified(LogicExpr::Exists, -Wide, Wide,
                             boolean(LogicExpr::Eq, square(i()),
                                     mathLiteral(2)))),
            std::optional<bool>(false));
  // A cubic with three roots near 10^6: i^3 - 3*10^6 i^2 + ... <= 0 between.
  auto cubic = [&] {
    // (i - 999999) * (i - 1000000) * (i - 1000001)
    return node(
        LogicExpr::Mul, math(),
        node(LogicExpr::Mul, math(),
             node(LogicExpr::Sub, math(), i(), mathLiteral(999999)),
             node(LogicExpr::Sub, math(), i(), mathLiteral(1000000))),
        node(LogicExpr::Sub, math(), i(), mathLiteral(1000001)));
  };
  EXPECT_EQ(truth(quantified(LogicExpr::Forall, 1000001, Wide,
                             boolean(LogicExpr::Ge, cubic(), mathLiteral(0)))),
            std::optional<bool>(true));
  EXPECT_EQ(truth(quantified(LogicExpr::Exists, -Wide, 999999,
                             boolean(LogicExpr::Gt, cubic(), mathLiteral(0)))),
            std::optional<bool>(false));
  EXPECT_EQ(truth(quantified(LogicExpr::Exists, -Wide, Wide,
                             boolean(LogicExpr::Eq, cubic(), mathLiteral(0)))),
            std::optional<bool>(true));
}

TEST(CertifyTest, FreeSymbolsComeFromTheModel) {
  ObligationModule Module;
  const LogicSort U8 = LogicSort::bitVector(8, false);
  TableModel Model;
  Model.Constants["x"] = integerValue(200);
  Model.Valid["64"] = true;
  Expr Query =
      boolean(LogicExpr::And,
              boolean(LogicExpr::Eq, variable("x", U8), literal("200", U8)),
              node(LogicExpr::ValidPtr, LogicSort::boolSort(),
                   literal("64", LogicSort::pointer())));
  EXPECT_EQ(certifyCounterexample(Module, *Query, Model).Outcome,
            CertifyOutcome::Certified);
  // A value outside its machine sort is an adapter defect.
  Model.Constants["x"] = integerValue(300);
  EXPECT_EQ(certifyCounterexample(Module, *Query, Model).Outcome,
            CertifyOutcome::Undetermined);
  Model.Constants.clear();
  CertifyResult Missing = certifyCounterexample(Module, *Query, Model);
  EXPECT_EQ(Missing.Outcome, CertifyOutcome::Undetermined);
  EXPECT_NE(Missing.Detail.find("x"), std::string::npos);
}

// --- Logical functions
// --------------------------------------------------------

/// triangle(n) = n <= 0 ? 0 : n + triangle(n - 1)
LogicFunctionDecl triangle(unsigned Fuel = 1, bool WithDefinition = true) {
  LogicFunctionDecl F;
  F.Identity = "triangle_id";
  F.DisplayName = "triangle";
  F.Parameters.push_back({"n", math()});
  F.ResultSort = math();
  F.DefinitionFuel = Fuel;
  if (!WithDefinition)
    return F;
  auto n = [] { return variable("n", math()); };
  F.StepDefinition =
      node(LogicExpr::Ite, math(), boolean(LogicExpr::Le, n(), mathLiteral(0)),
           mathLiteral(0), node(LogicExpr::Add, math(), n(), call(F, [&] {
                                  std::vector<Expr> Args;
                                  Args.push_back(node(LogicExpr::Sub, math(),
                                                      n(), mathLiteral(1)));
                                  return Args;
                                }())));
  for (unsigned I = 0; I != Fuel; ++I)
    F.DefinitionLevels.push_back(clone(*F.StepDefinition));
  return F;
}

ObligationModule withFunction(LogicFunctionDecl F) {
  ObligationModule Module;
  std::string Identity = F.Identity;
  Module.LogicFunctions.emplace(Identity, std::move(F));
  return Module;
}

/// triangle(x) != Closed(x), the query of `post(result == triangle(x))`.
Expr triangleQuery(const LogicFunctionDecl &F, int64_t Numerator) {
  auto x = [] { return variable("x", math()); };
  std::vector<Expr> Args;
  Args.push_back(x());
  Expr Closed =
      node(LogicExpr::Div, math(),
           node(LogicExpr::Mul, math(), x(),
                node(LogicExpr::Add, math(), x(), mathLiteral(Numerator))),
           mathLiteral(2));
  return boolean(LogicExpr::Ne, call(F, std::move(Args)), std::move(Closed));
}

TEST(CertifyTest, DefinitionsDecideSpecApplications) {
  ObligationModule Module = withFunction(triangle());
  const LogicFunctionDecl &F = Module.LogicFunctions.at("triangle_id");
  TableModel Model;
  Model.Constants["x"] = integerValue(5);
  Model.DefaultApplication = integerValue(-42);
  // triangle(5) = 15 = 5 * 6 / 2, but the model claims -42 there.
  Expr Correct = triangleQuery(F, 1);
  CertifyResult Refuted = certifyCounterexample(Module, *Correct, Model);
  ASSERT_EQ(Refuted.Outcome, CertifyOutcome::Disputed);
  std::set<std::string> Disputed;
  for (const SpecDispute &Dispute : Refuted.Disputes)
    Disputed.insert(Dispute.Arguments.front().key());
  EXPECT_EQ(Disputed, (std::set<std::string>{"0", "1", "2", "3", "4", "5"}));
  // 15 != 5 * 4 / 2: a real counterexample whatever the model claims.
  Expr Wrong = triangleQuery(F, -1);
  EXPECT_EQ(certifyCounterexample(Module, *Wrong, Model).Outcome,
            CertifyOutcome::Certified);
  // A model that agrees with the definitions cannot satisfy a true query.
  for (int64_t N = 0; N <= 5; ++N)
    Model.Applications[TableModel::key(F.Identity, {integerValue(N)})] =
        integerValue(N * (N + 1) / 2);
  EXPECT_EQ(certifyCounterexample(Module, *Correct, Model).Outcome,
            CertifyOutcome::Inconsistent);
}

TEST(CertifyTest, RefinementGivesInstancesOnceThenStops) {
  ObligationModule Module = withFunction(triangle());
  const LogicFunctionDecl &F = Module.LogicFunctions.at("triangle_id");
  TableModel Model;
  Model.Constants["x"] = integerValue(3);
  Model.DefaultApplication = integerValue(100);
  Expr Query = triangleQuery(F, 1);
  DefinitionRefinement Refinement(Module);
  CertifyResult First = certifyCounterexample(Module, *Query, Model);
  RefinementDecision Decision = Refinement.next(First);
  ASSERT_EQ(Decision.Next, RefinementDecision::Action::Refine);
  EXPECT_EQ(Decision.Instances.size(), First.Disputes.size());
  EXPECT_TRUE(Refinement.refined());
  // Instances already given cannot explain the same model again.
  RefinementDecision Again = Refinement.next(First);
  EXPECT_EQ(Again.Next, RefinementDecision::Action::Stop);
  EXPECT_EQ(Again.Reason, VerifyReason::InvalidBackendResult);
  RefinementDecision Exhausted =
      Refinement.exhausted("then z3 returned unknown");
  EXPECT_EQ(Exhausted.Reason, VerifyReason::SpecFuel);
  EXPECT_NE(Exhausted.Message.find("triangle"), std::string::npos);
  EXPECT_NE(Exhausted.Message.find("z3 returned unknown"), std::string::npos);
}

TEST(CertifyTest, HiddenInstancesSteerSearchButNeverProve) {
  ObligationModule Module = withFunction(triangle(/*Fuel=*/0));
  const LogicFunctionDecl &F = Module.LogicFunctions.at("triangle_id");
  TableModel Model;
  Model.Constants["x"] = integerValue(4);
  Model.DefaultApplication = integerValue(0);
  Expr Query = triangleQuery(F, 1);
  CertifyResult Result = certifyCounterexample(Module, *Query, Model);
  ASSERT_EQ(Result.Outcome, CertifyOutcome::Disputed);
  DefinitionRefinement Refinement(Module);
  EXPECT_FALSE(Refinement.unsatisfiable());
  RefinementDecision Decision = Refinement.next(Result);
  EXPECT_EQ(Decision.Next, RefinementDecision::Action::Refine);
  // An unsat that may rely on hidden instances is not a proof.
  std::optional<RefinementDecision> Unsat = Refinement.unsatisfiable();
  ASSERT_TRUE(Unsat);
  EXPECT_EQ(Unsat->Reason, VerifyReason::SpecHidden);
  EXPECT_TRUE(Unsat->NoCounterexample);
  EXPECT_NE(Unsat->Message.find("triangle"), std::string::npos);
  RefinementDecision Exhausted = Refinement.exhausted();
  EXPECT_EQ(Exhausted.Reason, VerifyReason::SpecHidden);
  EXPECT_FALSE(Exhausted.NoCounterexample);
  // The search among a hidden function's values is bounded separately.
  DefinitionRefinement Bounded(Module, /*MaxHiddenRounds=*/2);
  for (int64_t X : {4, 5}) {
    Model.Constants["x"] = integerValue(X);
    EXPECT_EQ(Bounded.next(certifyCounterexample(Module, *Query, Model)).Next,
              RefinementDecision::Action::Refine);
  }
  Model.Constants["x"] = integerValue(6);
  RefinementDecision Third =
      Bounded.next(certifyCounterexample(Module, *Query, Model));
  EXPECT_EQ(Third.Next, RefinementDecision::Action::Stop);
  EXPECT_EQ(Third.Reason, VerifyReason::SpecHidden);
}

TEST(CertifyTest, ArchivedFunctionsWithoutDefinitionsStayUnchecked) {
  ObligationModule Module =
      withFunction(triangle(/*Fuel=*/0, /*WithDefinition=*/false));
  const LogicFunctionDecl &F = Module.LogicFunctions.at("triangle_id");
  TableModel Model;
  Model.Constants["x"] = integerValue(4);
  Model.DefaultApplication = integerValue(0);
  CertifyResult Result =
      certifyCounterexample(Module, *triangleQuery(F, 1), Model);
  EXPECT_EQ(Result.Outcome, CertifyOutcome::Undetermined);
  EXPECT_EQ(DefinitionRefinement(Module).next(Result).Reason,
            VerifyReason::UncheckedCounterexample);
}

TEST(CertifyTest, DeepDefinitionsReportFuel) {
  ObligationModule Module = withFunction(triangle());
  const LogicFunctionDecl &F = Module.LogicFunctions.at("triangle_id");
  TableModel Model;
  Model.Constants["x"] = integerValue(1000000);
  Model.DefaultApplication = integerValue(0);
  CertifyResult Result =
      certifyCounterexample(Module, *triangleQuery(F, 1), Model);
  ASSERT_EQ(Result.Outcome, CertifyOutcome::Undetermined);
  EXPECT_TRUE(Result.DefinitionTooDeep);
  EXPECT_NE(Result.Detail.find("triangle"), std::string::npos);
  EXPECT_EQ(DefinitionRefinement(Module).next(Result).Reason,
            VerifyReason::SpecFuel);
  // Within the limits, a long chain evaluates through memoized definitions.
  Model.Constants["x"] = integerValue(5000);
  EXPECT_EQ(certifyCounterexample(Module, *triangleQuery(F, -1), Model).Outcome,
            CertifyOutcome::Certified);
}

TEST(CertifyTest, MutualRecursionAndMachineResults) {
  // even(n) = n == 0 || odd(n - 1); odd(n) = n != 0 && even(n - 1), over u8.
  const LogicSort U8 = LogicSort::bitVector(8, false);
  LogicFunctionDecl Even, Odd;
  Even.Identity = "even_id";
  Even.DisplayName = "even";
  Odd.Identity = "odd_id";
  Odd.DisplayName = "odd";
  for (LogicFunctionDecl *F : {&Even, &Odd}) {
    F->Parameters.push_back({"n", U8});
    F->ResultSort = LogicSort::boolSort();
    F->DefinitionFuel = 1;
  }
  auto n = [&] { return variable("n", U8); };
  auto pred = [&] {
    std::vector<Expr> Args;
    Args.push_back(node(LogicExpr::Sub, U8, n(), literal("1", U8)));
    return Args;
  };
  Even.StepDefinition =
      boolean(LogicExpr::Or, boolean(LogicExpr::Eq, n(), literal("0", U8)),
              call(Odd, pred()));
  Odd.StepDefinition =
      boolean(LogicExpr::And, boolean(LogicExpr::Ne, n(), literal("0", U8)),
              call(Even, pred()));
  ObligationModule Module;
  Module.LogicFunctions.emplace(Even.Identity, std::move(Even));
  Module.LogicFunctions.emplace(Odd.Identity, std::move(Odd));
  const LogicFunctionDecl &E = Module.LogicFunctions.at("even_id");
  TableModel Model;
  Model.Constants["k"] = integerValue(201);
  Model.DefaultApplication = LogicValue::boolean(true);
  std::vector<Expr> Args;
  Args.push_back(variable("k", U8));
  Expr ClaimsEven = call(E, std::move(Args));
  CertifyResult Result = certifyCounterexample(Module, *ClaimsEven, Model);
  EXPECT_EQ(Result.Outcome, CertifyOutcome::Disputed);
  std::vector<Expr> OddArgs;
  OddArgs.push_back(variable("k", U8));
  Expr ClaimsOdd = negation(call(E, std::move(OddArgs)));
  EXPECT_EQ(certifyCounterexample(Module, *ClaimsOdd, Model).Outcome,
            CertifyOutcome::Certified);
}

// --- Agreement with the solver encodings
// --------------------------------------

/// Random ground terms over every operator, sort, and conversion.
class TermGenerator {
  std::mt19937_64 &Random;

  unsigned pick(unsigned N) { return static_cast<unsigned>(Random() % N); }

  APInt bits(unsigned W) {
    llvm::SmallVector<uint64_t, 4> Words((W + 63) / 64);
    for (uint64_t &Word : Words)
      Word = pick(4) == 0 ? 0 : Random() >> pick(64);
    return APInt(W, Words);
  }

public:
  explicit TermGenerator(std::mt19937_64 &Random) : Random(Random) {}

  LogicSort machineSort() {
    static const unsigned Choices[] = {1, 5, 8, 16, 32, 64};
    return LogicSort::bitVector(Choices[pick(6)], pick(2) == 0);
  }

  Expr machine(LogicSort Sort, unsigned Depth) {
    if (Depth == 0 || pick(4) == 0)
      return literal(bits(Sort.BitWidth), Sort);
    switch (pick(9)) {
    case 0: {
      static const LogicExpr::Kind Kinds[] = {
          LogicExpr::Add,   LogicExpr::Sub,   LogicExpr::Mul,
          LogicExpr::Div,   LogicExpr::Rem,   LogicExpr::BitAnd,
          LogicExpr::BitOr, LogicExpr::BitXor};
      return node(Kinds[pick(8)], Sort, machine(Sort, Depth - 1),
                  machine(Sort, Depth - 1));
    }
    case 1:
      return node(pick(2) ? LogicExpr::Shl : LogicExpr::Shr, Sort,
                  machine(Sort, Depth - 1),
                  literal(APInt(Sort.BitWidth, pick(Sort.BitWidth + 2),
                                /*isSigned=*/false, /*implicitTrunc=*/true),
                          LogicSort::bitVector(Sort.BitWidth, pick(2) == 0)));
    case 2:
      return node(pick(2) ? LogicExpr::Neg : LogicExpr::BitNot, Sort,
                  machine(Sort, Depth - 1));
    case 3:
      return node(LogicExpr::Ite, Sort, formula(Depth - 1),
                  machine(Sort, Depth - 1), machine(Sort, Depth - 1));
    case 4:
      return node(LogicExpr::BvResize, Sort, machine(machineSort(), Depth - 1));
    case 5:
      return node(LogicExpr::IntToBv, Sort, mathematical(Depth - 1));
    default:
      return node(LogicExpr::Add, Sort, machine(Sort, Depth - 1),
                  literal(bits(Sort.BitWidth), Sort));
    }
  }

  Expr mathematical(unsigned Depth) {
    if (Depth == 0 || pick(4) == 0)
      return literal(decimal(bits(72), true), math());
    switch (pick(5)) {
    case 0: {
      static const LogicExpr::Kind Kinds[] = {LogicExpr::Add, LogicExpr::Sub,
                                              LogicExpr::Mul, LogicExpr::Div,
                                              LogicExpr::Rem};
      return node(Kinds[pick(5)], math(), mathematical(Depth - 1),
                  mathematical(Depth - 1));
    }
    case 1:
      return node(LogicExpr::Neg, math(), mathematical(Depth - 1));
    case 2:
      return node(LogicExpr::BvToInt, math(),
                  machine(machineSort(), Depth - 1));
    case 3:
      return node(LogicExpr::Ite, math(), formula(Depth - 1),
                  mathematical(Depth - 1), mathematical(Depth - 1));
    default:
      return node(LogicExpr::Mul, math(), mathematical(Depth - 1),
                  literal("3", math()));
    }
  }

  Expr formula(unsigned Depth) {
    if (Depth == 0)
      return boolLiteral(pick(2) == 0);
    static const LogicExpr::Kind Comparisons[] = {LogicExpr::Lt, LogicExpr::Le,
                                                  LogicExpr::Gt, LogicExpr::Ge,
                                                  LogicExpr::Eq, LogicExpr::Ne};
    switch (pick(5)) {
    case 0: {
      LogicSort Sort = machineSort();
      return boolean(Comparisons[pick(6)], machine(Sort, Depth - 1),
                     machine(Sort, Depth - 1));
    }
    case 1:
      return boolean(Comparisons[pick(6)], mathematical(Depth - 1),
                     mathematical(Depth - 1));
    case 2: {
      static const LogicOverflowOp Ops[] = {
          LogicOverflowOp::Add, LogicOverflowOp::Sub, LogicOverflowOp::Mul,
          LogicOverflowOp::SignedDiv, LogicOverflowOp::Neg};
      const LogicOverflowOp Op = Ops[pick(5)];
      LogicSort Sort = machineSort();
      std::vector<Expr> Operands;
      Operands.push_back(machine(Sort, Depth - 1));
      if (Op != LogicOverflowOp::Neg)
        Operands.push_back(machine(machineSort(), Depth - 1));
      Expr Check = node(LogicExpr::NoOverflow, LogicSort::boolSort(),
                        std::move(Operands));
      Check->OverflowOp = Op;
      return Check;
    }
    case 3:
      return boolean(pick(2) ? LogicExpr::And : LogicExpr::Or,
                     formula(Depth - 1), formula(Depth - 1));
    default:
      return negation(formula(Depth - 1));
    }
  }
};

ObligationModule goalModule(Expr Goal) {
  ObligationModule M;
  M.FunctionName = "certify_oracle";
  M.FunctionIdentity = "certify_oracle";
  Obligation Item;
  Item.Id = "oracle";
  Item.Goal = clone(*Goal);
  Item.CounterexampleQuery = negation(clone(*Goal));
  M.Obligations.push_back(std::move(Item));
  M.CorrectnessGoal = clone(*Goal);
  M.CounterexampleQuery = negation(std::move(Goal));
  auto Features = validateObligationModule(M);
  EXPECT_TRUE(static_cast<bool>(Features))
      << (Features ? "" : llvm::toString(Features.takeError()));
  if (Features)
    M.RequiredFeatures = *Features;
  return M;
}

Expr valueLiteral(const LogicValue &Value, const LogicSort &Sort,
                  bool Corrupt) {
  if (Sort.Kind == LogicSortKind::Bool)
    return boolLiteral(Value.Truth != Corrupt);
  const CertInt Integer = Corrupt ? Value.Integer + CertInt(1) : Value.Integer;
  return literal(Integer.toDecimal(), Sort);
}

bool haveCVC5() {
  static const bool Available =
      static_cast<bool>(llvm::sys::findProgramByName("cvc5"));
  return Available;
}

/// The certifier's value is the one each encoding proves, and the solver
/// reports a checked counterexample for the corrupted value.
void expectAgreement(BackendKind Solver, unsigned Terms, uint64_t Seed) {
  // CPPVERIFY_CERTIFY_TERMS=N widens the sweep.
  if (const char *Override = std::getenv("CPPVERIFY_CERTIFY_TERMS"))
    Terms = static_cast<unsigned>(std::strtoul(Override, nullptr, 10));
  std::mt19937_64 Random(Seed);
  TermGenerator Generate(Random);
  for (unsigned I = 0; I != Terms; ++I) {
    Expr Term;
    switch (I % 3) {
    case 0:
      Term = Generate.machine(Generate.machineSort(), 3);
      break;
    case 1:
      Term = Generate.mathematical(3);
      break;
    default:
      Term = Generate.formula(3);
      break;
    }
    ObligationModule Empty;
    TableModel Model;
    std::string Failure;
    std::optional<LogicValue> Value =
        evaluateTerm(Empty, *Term, Model, {}, &Failure);
    ASSERT_TRUE(Value) << Failure;
    for (MachineIntegerEncoding Encoding :
         {MachineIntegerEncoding::Integer, MachineIntegerEncoding::BitVector})
      for (bool Corrupt : {false, true}) {
        Expr Goal = boolean(LogicExpr::Eq, clone(*Term),
                            valueLiteral(*Value, Term->Sort, Corrupt));
        BackendExecutionOptions Execution;
        Execution.SolverTimeoutMs = 60000;
        Execution.IntegerEncoding = Encoding;
        auto Backend = createVerifyBackend(Solver, nullptr, 0, Execution);
        VerifyResult Result = Backend->verify(goalModule(std::move(Goal)));
        EXPECT_EQ(Result.Status,
                  Corrupt ? VerifyStatus::Failed : VerifyStatus::Verified)
            << "term " << I << " seed " << Seed << " encoding "
            << machineIntegerEncodingName(Encoding).str() << ": "
            << Result.Message;
      }
  }
}

TEST(CertifyTest, AgreesWithZ3Encodings) {
  expectAgreement(BackendKind::Z3, 240, 23);
}

TEST(CertifyTest, AgreesWithCVC5Encodings) {
  if (!haveCVC5())
    GTEST_SKIP() << "cvc5 is not installed";
  expectAgreement(BackendKind::CVC5, 60, 29);
}

} // namespace

// --- Presburger arithmetic --------------------------------------------------

TEST(CertifyTest, PresburgerDecidesClosedFormulas) {
  namespace pb = clang::verify::presburger;
  const pb::Linear X = pb::Linear::variable("x");
  const pb::Linear Y = pb::Linear::variable("y");
  const pb::Linear Z = pb::Linear::variable("z");
  auto c = [](int64_t V) { return pb::Linear::constant(CertInt(V)); };
  auto two = [](const pb::Linear &T) { return T.scaled(CertInt(2)); };
  auto decide = [](const pb::FormulaPtr &F) { return pb::decide(F, 100000); };
  EXPECT_EQ(decide(pb::forall("x", pb::exists("y", pb::equal(Y, X + c(1))))),
            true);
  EXPECT_EQ(decide(pb::forall("x", pb::exists("y", pb::equal(two(Y), X)))),
            false);
  EXPECT_EQ(decide(pb::forall(
                "x", pb::exists(
                         "y", pb::disjunction({pb::equal(two(Y), X),
                                               pb::equal(two(Y) + c(1), X)})))),
            true);
  EXPECT_EQ(decide(pb::exists("x", pb::equal(two(X), c(3)))), false);
  EXPECT_EQ(decide(pb::forall(
                "x", pb::disjunction({pb::negation(pb::divides(CertInt(6), X)),
                                      pb::divides(CertInt(3), X)}))),
            true);
  EXPECT_EQ(decide(pb::forall(
                "x", pb::disjunction({pb::negation(pb::divides(CertInt(3), X)),
                                      pb::divides(CertInt(6), X)}))),
            false);
  // x = 3: 3x + 1 = 10 and x is odd.
  EXPECT_EQ(decide(pb::exists(
                "x", pb::conjunction(
                         {pb::lessEqual(X.scaled(CertInt(3)) + c(1), c(10)),
                          pb::lessEqual(c(10), X.scaled(CertInt(3)) + c(4)),
                          pb::negation(pb::divides(CertInt(2), X))}))),
            true);
  // Between x and x + 2 lies only x + 1, which is odd for even x.
  EXPECT_EQ(decide(pb::forall(
                "x", pb::exists("y", pb::conjunction(
                                         {pb::less(X, Y), pb::less(Y, X + c(2)),
                                          pb::divides(CertInt(2), Y)})))),
            false);
  EXPECT_EQ(
      decide(pb::forall(
          "x",
          pb::exists("y", pb::forall("z", pb::disjunction({pb::lessEqual(Z, Y),
                                                           pb::less(X, Z)}))))),
      true);
}

TEST(CertifyTest, PresburgerAgreesWithZ3) {
  // Random sentences over three variables: Cooper's elimination and Z3 must
  // agree wherever Z3 decides.
  namespace pb = clang::verify::presburger;
  std::mt19937_64 Random(7);
  auto pick = [&](int64_t Low, int64_t High) {
    return std::uniform_int_distribution<int64_t>(Low, High)(Random);
  };
  z3::context Ctx;
  const char *Names[] = {"a", "b", "c"};
  unsigned Compared = 0;
  unsigned TooLarge = 0;
  for (unsigned Round = 0; Round != 300; ++Round) {
    const unsigned Depth = static_cast<unsigned>(pick(1, 3));
    auto term = [&](pb::Linear &P, z3::expr &E) {
      P = pb::Linear::constant(CertInt(pick(-6, 6)));
      E = Ctx.int_val(static_cast<int>(P.Constant.bits(64).getSExtValue()));
      for (unsigned V = 0; V != Depth; ++V) {
        const int64_t Coefficient = pick(-3, 3);
        P = P + pb::Linear::variable(Names[V]).scaled(CertInt(Coefficient));
        E = E + Ctx.int_val(static_cast<int>(Coefficient)) *
                    Ctx.int_const(Names[V]);
      }
    };
    std::function<std::pair<pb::FormulaPtr, z3::expr>(unsigned)> formula =
        [&](unsigned Level) -> std::pair<pb::FormulaPtr, z3::expr> {
      if (Level == 0 || pick(0, 2) == 0) {
        pb::Linear P;
        z3::expr E(Ctx);
        term(P, E);
        switch (pick(0, 2)) {
        case 0:
          return {pb::atMostZero(P), E <= 0};
        case 1:
          return {pb::zero(P), E == 0};
        default: {
          const int64_t D = pick(2, 3);
          return {pb::divides(CertInt(D), P),
                  z3::mod(E, Ctx.int_val(static_cast<int>(D))) == 0};
        }
        }
      }
      auto [L, LE] = formula(Level - 1);
      auto [R, RE] = formula(Level - 1);
      switch (pick(0, 2)) {
      case 0:
        return {pb::conjunction({L, R}), LE && RE};
      case 1:
        return {pb::disjunction({L, R}), LE || RE};
      default:
        return {pb::negation(L), !LE};
      }
    };
    auto [Body, BodyE] = formula(2);
    pb::FormulaPtr Sentence = Body;
    z3::expr SentenceE = BodyE;
    for (unsigned V = Depth; V-- > 0;) {
      z3::expr_vector Bound(Ctx);
      Bound.push_back(Ctx.int_const(Names[V]));
      if (pick(0, 1)) {
        Sentence = pb::forall(Names[V], Sentence);
        SentenceE = z3::forall(Bound, SentenceE);
      } else {
        Sentence = pb::exists(Names[V], Sentence);
        SentenceE = z3::exists(Bound, SentenceE);
      }
    }
    std::optional<bool> Ours = pb::decide(Sentence, 1000000);
    if (!Ours) {
      ++TooLarge;
      continue;
    }
    z3::solver Solver(Ctx);
    z3::params Params(Ctx);
    Params.set("timeout", 5000u);
    Solver.set(Params);
    Solver.add(SentenceE);
    const z3::check_result Theirs = Solver.check();
    if (Theirs == z3::unknown)
      continue;
    ++Compared;
    EXPECT_EQ(*Ours, Theirs == z3::sat) << SentenceE.to_string();
  }
  EXPECT_GT(Compared, 250u);
  EXPECT_LT(TooLarge, 15u);
}

TEST(CertifyTest, NestedUnboundedQuantifiersAreDecided) {
  // s = [3, 1, 2]: not every element has a larger one, but every element
  // has one at least as large.
  TableModel Model;
  Model.Constants["s"] =
      LogicValue::sequence({CertInt(3), CertInt(1), CertInt(2)});
  ObligationModule Module;
  auto read = [](const char *Binder) {
    Expr Read = node(LogicExpr::Collection, math(),
                     variable("s", LogicSort::collection(LogicSortKind::Seq)),
                     variable(Binder, math()));
    Read->CollectionOp = LogicCollectionOp::SeqIndex;
    return Read;
  };
  auto length = [] {
    Expr Length =
        node(LogicExpr::Collection, math(),
             variable("s", LogicSort::collection(LogicSortKind::Seq)));
    Length->CollectionOp = LogicCollectionOp::SeqLength;
    return Length;
  };
  auto inside = [&](const char *Binder) {
    return node(
        LogicExpr::And, LogicSort::boolSort(),
        boolean(LogicExpr::Le, mathLiteral(0), variable(Binder, math())),
        boolean(LogicExpr::Lt, variable(Binder, math()), length()));
  };
  auto everyHasAbove = [&](LogicExpr::Kind Compare) {
    Expr Inner = node(LogicExpr::Exists, LogicSort::boolSort(),
                      node(LogicExpr::And, LogicSort::boolSort(), inside("j"),
                           boolean(Compare, read("j"), read("i"))));
    Inner->Binder = "j";
    Expr Outer = node(LogicExpr::Forall, LogicSort::boolSort(),
                      node(LogicExpr::Or, LogicSort::boolSort(),
                           negation(inside("i")), std::move(Inner)));
    Outer->Binder = "i";
    return Outer;
  };
  EXPECT_EQ(certifyCounterexample(
                Module, *negation(everyHasAbove(LogicExpr::Gt)), Model)
                .Outcome,
            CertifyOutcome::Certified);
  EXPECT_EQ(certifyCounterexample(Module, *everyHasAbove(LogicExpr::Ge), Model)
                .Outcome,
            CertifyOutcome::Certified);
  EXPECT_EQ(certifyCounterexample(Module, *everyHasAbove(LogicExpr::Gt), Model)
                .Outcome,
            CertifyOutcome::Inconsistent);
}
