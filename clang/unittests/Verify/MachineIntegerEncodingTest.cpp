//===- MachineIntegerEncodingTest.cpp - Exact machine-integer encodings ---===//
//
// Checks every machine-integer operator against llvm::APInt under each
// encoding; corrupted expectations must be refuted.
//
//===----------------------------------------------------------------------===//

#include "Backend/CVC5Backend.h"
#include "Backend/VerifyBackend.h"
#include "Backend/Z3Encode.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/Support/Program.h"
#include "gtest/gtest.h"
#include <chrono>
#include <functional>
#include <optional>
#include <random>

using namespace clang::verify;
using llvm::APInt;

namespace {

using Expr = std::unique_ptr<LogicExpr>;

LogicSort bitVector(unsigned Width, bool Signed) {
  return LogicSort::bitVector(Width, Signed);
}

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

Expr literal(const APInt &Value, LogicSort Sort) {
  Expr E = leaf(LogicExpr::IntLit, Sort);
  E->IntVal = decimal(Value, Sort.Signedness == LogicSignedness::Signed);
  return E;
}

Expr mathLiteral(const APInt &Value, bool Signed) {
  Expr E = leaf(LogicExpr::IntLit, LogicSort::mathematicalInteger(64, true));
  E->IntVal = decimal(Value, Signed);
  return E;
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

Expr conjunction(std::vector<Expr> Items) {
  if (Items.empty())
    return leaf(LogicExpr::True, LogicSort::boolSort());
  Expr Result = std::move(Items.front());
  for (size_t I = 1; I != Items.size(); ++I)
    Result = boolean(LogicExpr::And, std::move(Result), std::move(Items[I]));
  return Result;
}

/// `Guard -> Body` as the canonical IR spells it.
Expr implies(Expr Guard, Expr Body) {
  return boolean(LogicExpr::Or,
                 node(LogicExpr::Not, LogicSort::boolSort(), std::move(Guard)),
                 std::move(Body));
}

ObligationModule
makeModule(Expr Goal, std::map<std::string, LogicFunctionDecl> Functions = {}) {
  ObligationModule M;
  M.FunctionName = "encoding_oracle";
  M.FunctionIdentity = "encoding_oracle";
  M.LogicFunctions = std::move(Functions);
  Obligation Item;
  Item.Id = "oracle";
  Item.Goal = clone(*Goal);
  Item.CounterexampleQuery =
      node(LogicExpr::Not, LogicSort::boolSort(), clone(*Goal));
  M.Obligations.push_back(std::move(Item));
  M.CorrectnessGoal = clone(*Goal);
  M.CounterexampleQuery =
      node(LogicExpr::Not, LogicSort::boolSort(), std::move(Goal));
  auto Features = validateObligationModule(M);
  EXPECT_TRUE(static_cast<bool>(Features))
      << (Features ? "" : llvm::toString(Features.takeError()));
  if (Features)
    M.RequiredFeatures = *Features;
  return M;
}

struct Configuration {
  BackendKind Solver;
  MachineIntegerEncoding Encoding;
  std::string name() const {
    return std::string(Solver == BackendKind::Z3 ? "z3" : "cvc5") + "/" +
           machineIntegerEncodingName(Encoding).str();
  }
};

bool haveCVC5() {
  static const bool Available =
      static_cast<bool>(llvm::sys::findProgramByName("cvc5"));
  return Available;
}

using Encodings = std::vector<MachineIntegerEncoding>;

/// Auto resolves to one of these per query; AutoResolution checks that choice.
const Encodings ExactEncodings = {MachineIntegerEncoding::Integer,
                                  MachineIntegerEncoding::BitVector};

std::vector<Configuration>
configurations(bool IncludeCVC5, const Encodings &Selected = ExactEncodings) {
  std::vector<Configuration> Result;
  for (MachineIntegerEncoding Encoding : Selected) {
    Result.push_back({BackendKind::Z3, Encoding});
    if (IncludeCVC5 && haveCVC5())
      Result.push_back({BackendKind::CVC5, Encoding});
  }
  return Result;
}

MachineIntegerEncoding z3Encoding(const ObligationModule &M,
                                  MachineIntegerEncoding Requested,
                                  std::string *Dump = nullptr);

VerifyResult run(const ObligationModule &M, const Configuration &Config,
                 unsigned TimeoutMs = 60000) {
  if (std::getenv("CPPVERIFY_ORACLE_DUMP") &&
      Config.Solver == BackendKind::Z3) {
    std::string Dump;
    z3Encoding(M, Config.Encoding, &Dump);
    llvm::errs() << "z3 query [" << Config.name() << "]:\n" << Dump;
  }
  BackendExecutionOptions Execution;
  Execution.SolverTimeoutMs = TimeoutMs;
  Execution.IntegerEncoding = Config.Encoding;
  auto Backend = createVerifyBackend(Config.Solver, nullptr, 0, Execution);
  const auto Start = std::chrono::steady_clock::now();
  VerifyResult Result = Backend->verify(M);
  const auto Elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(
      std::chrono::steady_clock::now() - Start);
  if (Elapsed.count() > 2000)
    llvm::errs() << "slow query: " << Config.name() << " took "
                 << Elapsed.count() << " ms\n";
  return Result;
}

const char *statusName(VerifyStatus Status) {
  switch (Status) {
  case VerifyStatus::Verified:
    return "verified";
  case VerifyStatus::Failed:
    return "failed";
  case VerifyStatus::Unresolved:
    return "unresolved";
  default:
    return "other";
  }
}

using Tolerance = std::function<bool(const Configuration &)>;

/// Proves the goal and refutes its corrupted twin; a tolerated configuration
/// may stay unresolved but never decide wrongly.
void expectExact(const std::function<Expr(bool Corrupt)> &Build,
                 const std::string &What, bool IncludeCVC5 = true,
                 const Encodings &Selected = ExactEncodings,
                 const Tolerance &MayStayUnresolved = nullptr) {
  for (const Configuration &Config : configurations(IncludeCVC5, Selected)) {
    if (std::getenv("CPPVERIFY_ORACLE_TRACE"))
      llvm::errs() << "case: " << What << " [" << Config.name() << "]\n";
    const bool Tolerated = MayStayUnresolved && MayStayUnresolved(Config);
    for (bool Corrupt : {false, true}) {
      const VerifyStatus Expected =
          Corrupt ? VerifyStatus::Failed : VerifyStatus::Verified;
      VerifyResult Result =
          run(makeModule(Build(Corrupt)), Config, Tolerated ? 10000 : 60000);
      if (Tolerated && Result.Status == VerifyStatus::Unresolved) {
        if (std::getenv("CPPVERIFY_ORACLE_TRACE"))
          llvm::errs() << "tolerated unresolved: " << What
                       << (Corrupt ? " (corrupted)" : "") << " ["
                       << Config.name() << "]\n";
        continue;
      }
      EXPECT_EQ(Result.Status, Expected)
          << What << (Corrupt ? " (corrupted)" : "") << " [" << Config.name()
          << "] " << statusName(Result.Status) << ": " << Result.Message;
    }
  }
}

// --- APInt reference semantics (SMT-LIB bit-vectors) -------------------------

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

LogicExpr::Kind kindOf(Binary Op) {
  switch (Op) {
  case Binary::Add:
    return LogicExpr::Add;
  case Binary::Sub:
    return LogicExpr::Sub;
  case Binary::Mul:
    return LogicExpr::Mul;
  case Binary::Div:
    return LogicExpr::Div;
  case Binary::Rem:
    return LogicExpr::Rem;
  case Binary::And:
    return LogicExpr::BitAnd;
  case Binary::Or:
    return LogicExpr::BitOr;
  case Binary::Xor:
    return LogicExpr::BitXor;
  case Binary::Shl:
    return LogicExpr::Shl;
  case Binary::Shr:
    return LogicExpr::Shr;
  case Binary::Lt:
    return LogicExpr::Lt;
  case Binary::Le:
    return LogicExpr::Le;
  case Binary::Gt:
    return LogicExpr::Gt;
  case Binary::Ge:
    return LogicExpr::Ge;
  case Binary::Eq:
    return LogicExpr::Eq;
  case Binary::Ne:
    return LogicExpr::Ne;
  }
  llvm_unreachable("unknown operator");
}

const char *nameOf(Binary Op) {
  static const char *Names[] = {"add", "sub", "mul", "div", "rem", "and",
                                "or",  "xor", "shl", "shr", "lt",  "le",
                                "gt",  "ge",  "eq",  "ne"};
  return Names[static_cast<unsigned>(Op)];
}

bool isComparison(Binary Op) { return Op >= Binary::Lt; }

bool isBitLevel(Binary Op) {
  return Op == Binary::And || Op == Binary::Or || Op == Binary::Xor ||
         Op == Binary::Shl || Op == Binary::Shr;
}

/// Forced integers reach variable operand bits only through bit-vector names
/// or int2bv, which may exhaust a solver (auto uses bit-vectors there).
Tolerance integerBitLevel(Binary Op, bool OnVariables) {
  if (!OnVariables || !isBitLevel(Op))
    return nullptr;
  return [](const Configuration &Config) {
    return Config.Encoding == MachineIntegerEncoding::Integer;
  };
}

/// Result bits for arithmetic operators, or a 1-bit truth value.
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

/// Operand values: exhaustive for tiny widths, edges plus random otherwise.
std::vector<APInt> operandValues(unsigned W, std::mt19937_64 &Random) {
  std::vector<APInt> Values;
  if (W <= 4) {
    for (uint64_t V = 0; V != (1ULL << W); ++V)
      Values.push_back(APInt(W, V));
    return Values;
  }
  for (const APInt &V :
       {APInt(W, 0), APInt(W, 1), APInt(W, 2), APInt(W, 3),
        APInt::getAllOnes(W), APInt::getAllOnes(W) - 1,
        APInt::getSignedMinValue(W), APInt::getSignedMinValue(W) + 1,
        APInt::getSignedMaxValue(W), APInt::getSignedMaxValue(W) - 1,
        APInt(W, W - 1), APInt(W, W)})
    Values.push_back(V);
  for (unsigned I = 0; I != 6; ++I) {
    llvm::SmallVector<uint64_t, 4> Words((W + 63) / 64);
    for (uint64_t &Word : Words)
      Word = Random();
    Values.push_back(APInt(W, Words));
  }
  return Values;
}

const unsigned Widths[] = {1, 2, 3, 4, 7, 8, 16, 32, 33, 64, 128};

// `op(a, b) == expected` for every sampled pair, on literals or variables.
Expr binaryGoal(Binary Op, unsigned W, bool Signed, bool OnVariables,
                bool Corrupt, std::mt19937_64 &Random,
                std::optional<bool> AmountSigned = std::nullopt) {
  const LogicSort Sort = bitVector(W, Signed);
  const LogicSort RightSort = bitVector(W, AmountSigned.value_or(Signed));
  const std::vector<APInt> Values = operandValues(W, Random);
  std::vector<Expr> Facts;
  bool Corrupted = false;
  for (const APInt &A : Values)
    for (const APInt &B : Values) {
      APInt Expected = reference(Op, A, B, Signed);
      if (Corrupt && !Corrupted) {
        Expected = isComparison(Op) ? ~Expected : Expected + 1;
        Corrupted = true;
      }
      auto operand = [&](const char *Name, const APInt &Value,
                         const LogicSort &OperandSort) {
        return OnVariables ? variable(Name, OperandSort)
                           : literal(Value, OperandSort);
      };
      Expr Applied =
          node(kindOf(Op), isComparison(Op) ? LogicSort::boolSort() : Sort,
               operand("x", A, Sort), operand("y", B, RightSort));
      Expr Fact =
          isComparison(Op)
              ? (Expected.isOne() ? std::move(Applied)
                                  : node(LogicExpr::Not, LogicSort::boolSort(),
                                         std::move(Applied)))
              : boolean(LogicExpr::Eq, std::move(Applied),
                        literal(Expected, Sort));
      if (OnVariables)
        Fact = implies(boolean(LogicExpr::And,
                               boolean(LogicExpr::Eq, variable("x", Sort),
                                       literal(A, Sort)),
                               boolean(LogicExpr::Eq, variable("y", RightSort),
                                       literal(B, RightSort))),
                       std::move(Fact));
      Facts.push_back(std::move(Fact));
    }
  return conjunction(std::move(Facts));
}

class BinaryOperatorTest : public ::testing::TestWithParam<Binary> {};

TEST_P(BinaryOperatorTest, MatchesAPIntUnderEveryEncoding) {
  const Binary Op = GetParam();
  for (unsigned W : Widths)
    for (bool Signed : {true, false})
      for (bool OnVariables : {false, true}) {
        const bool WithCVC5 = W == 1 || W == 3 || W == 8 || W == 64;
        std::string What = std::string(nameOf(Op)) + " i" + std::to_string(W) +
                           (Signed ? " signed" : " unsigned") +
                           (OnVariables ? " variables" : " literals");
        expectExact(
            [&](bool Corrupt) {
              std::mt19937_64 Random(W * 131 + Signed * 7 + OnVariables);
              return binaryGoal(Op, W, Signed, OnVariables, Corrupt, Random);
            },
            What, WithCVC5, ExactEncodings, integerBitLevel(Op, OnVariables));
      }
}

INSTANTIATE_TEST_SUITE_P(
    Operators, BinaryOperatorTest,
    ::testing::Values(Binary::Add, Binary::Sub, Binary::Mul, Binary::Div,
                      Binary::Rem, Binary::And, Binary::Or, Binary::Xor,
                      Binary::Shl, Binary::Shr, Binary::Lt, Binary::Le,
                      Binary::Gt, Binary::Ge, Binary::Eq, Binary::Ne),
    [](const ::testing::TestParamInfo<Binary> &Info) {
      return std::string(nameOf(Info.param));
    });

// C++ permits a shift amount whose signedness differs from the shifted value;
// the amount's bits are read unsigned, so a negative amount is out of range.
TEST(MachineIntegerEncodingTest, MixedSignednessShiftAmounts) {
  for (Binary Op : {Binary::Shl, Binary::Shr})
    for (unsigned W : {1u, 3u, 8u, 32u, 33u, 64u})
      for (bool Signed : {true, false})
        for (bool OnVariables : {false, true}) {
          std::string What =
              std::string(nameOf(Op)) + " i" + std::to_string(W) +
              (Signed ? "s" : "u") + " by i" + std::to_string(W) +
              (Signed ? "u" : "s") + (OnVariables ? " variables" : " literals");
          expectExact(
              [&](bool Corrupt) {
                std::mt19937_64 Random(W * 17 + Signed);
                return binaryGoal(Op, W, Signed, OnVariables, Corrupt, Random,
                                  !Signed);
              },
              What, W == 1 || W == 8 || W == 64, ExactEncodings,
              integerBitLevel(Op, OnVariables));
        }
}

// --- Unary operators and conversions -----------------------------------------

template <typename Fn> void forEachValue(unsigned W, Fn &&Visit) {
  std::mt19937_64 Random(W);
  for (const APInt &V : operandValues(W, Random))
    Visit(V);
}

TEST(MachineIntegerEncodingTest, NegationAndComplement) {
  for (unsigned W : Widths)
    for (bool Signed : {true, false})
      for (LogicExpr::Kind Kind : {LogicExpr::Neg, LogicExpr::BitNot})
        expectExact(
            [&](bool Corrupt) {
              const LogicSort Sort = bitVector(W, Signed);
              std::vector<Expr> Facts;
              forEachValue(W, [&](const APInt &V) {
                APInt Expected = Kind == LogicExpr::Neg ? -V : ~V;
                if (Corrupt && Facts.empty())
                  Expected += 1;
                Facts.push_back(boolean(LogicExpr::Eq,
                                        node(Kind, Sort, variable("x", Sort)),
                                        literal(Expected, Sort)));
                Facts.back() =
                    implies(boolean(LogicExpr::Eq, variable("x", Sort),
                                    literal(V, Sort)),
                            std::move(Facts.back()));
              });
              return conjunction(std::move(Facts));
            },
            std::string(Kind == LogicExpr::Neg ? "neg" : "not") + " i" +
                std::to_string(W) + (Signed ? " signed" : " unsigned"),
            W == 8);
}

TEST(MachineIntegerEncodingTest, ResizeAndReinterpret) {
  for (unsigned From : {1u, 3u, 8u, 32u, 64u})
    for (unsigned To : {1u, 3u, 8u, 32u, 64u, 128u})
      for (bool FromSigned : {true, false})
        for (bool ToSigned : {true, false})
          expectExact(
              [&](bool Corrupt) {
                const LogicSort Source = bitVector(From, FromSigned);
                const LogicSort Target = bitVector(To, ToSigned);
                std::vector<Expr> Facts;
                forEachValue(From, [&](const APInt &V) {
                  APInt Expected = To >= From
                                       ? (FromSigned ? V.sext(To) : V.zext(To))
                                       : V.trunc(To);
                  if (Corrupt && Facts.empty())
                    Expected += 1;
                  Facts.push_back(
                      implies(boolean(LogicExpr::Eq, variable("x", Source),
                                      literal(V, Source)),
                              boolean(LogicExpr::Eq,
                                      node(LogicExpr::BvResize, Target,
                                           variable("x", Source)),
                                      literal(Expected, Target))));
                });
                return conjunction(std::move(Facts));
              },
              "resize i" + std::to_string(From) + (FromSigned ? "s" : "u") +
                  " -> i" + std::to_string(To) + (ToSigned ? "s" : "u"),
              From == 8 && To == 32);
}

TEST(MachineIntegerEncodingTest, MathematicalConversions) {
  const LogicSort Math = LogicSort::mathematicalInteger(64, true);
  for (unsigned W : {1u, 3u, 8u, 32u, 64u, 128u})
    for (bool Signed : {true, false}) {
      const LogicSort Sort = bitVector(W, Signed);
      // BvToInt reads the value under the source signedness.
      expectExact(
          [&](bool Corrupt) {
            std::vector<Expr> Facts;
            forEachValue(W, [&](const APInt &V) {
              APInt Value = Signed ? V.sext(W + 2) : V.zext(W + 2);
              if (Corrupt && Facts.empty())
                Value += 1;
              Facts.push_back(implies(
                  boolean(LogicExpr::Eq, variable("x", Sort), literal(V, Sort)),
                  boolean(LogicExpr::Eq,
                          node(LogicExpr::BvToInt, Math, variable("x", Sort)),
                          mathLiteral(Value, true))));
            });
            return conjunction(std::move(Facts));
          },
          "bv2int i" + std::to_string(W) + (Signed ? "s" : "u"), W == 8);
      // IntToBv reduces any mathematical integer modulo 2^w.
      expectExact(
          [&](bool Corrupt) {
            std::vector<Expr> Facts;
            for (int64_t Base : {-3, -1, 0, 1, 2, 5}) {
              for (APInt Offset :
                   {APInt(W + 70, 0), APInt::getOneBitSet(W + 70, W),
                    APInt::getOneBitSet(W + 70, W + 3)}) {
                APInt Math = APInt(W + 70, Base, true) + Offset;
                if (Base < 0)
                  Math -= Offset + Offset;
                APInt Expected = Math.trunc(W);
                if (Corrupt && Facts.empty())
                  Expected += 1;
                Facts.push_back(boolean(
                    LogicExpr::Eq,
                    node(LogicExpr::IntToBv, Sort, mathLiteral(Math, true)),
                    literal(Expected, Sort)));
              }
            }
            return conjunction(std::move(Facts));
          },
          "int2bv i" + std::to_string(W) + (Signed ? "s" : "u"), W == 8);
    }
}

TEST(MachineIntegerEncodingTest, SignedOverflowPredicates) {
  struct Case {
    LogicOverflowOp Op;
    const char *Name;
  };
  for (Case C :
       {Case{LogicOverflowOp::Add, "add"}, Case{LogicOverflowOp::Sub, "sub"},
        Case{LogicOverflowOp::Mul, "mul"}, Case{LogicOverflowOp::Neg, "neg"},
        Case{LogicOverflowOp::SignedDiv, "sdiv"}})
    for (unsigned W : {3u, 8u, 32u, 64u})
      for (unsigned Other : {W, W / 2 + 1, W * 2})
        for (bool OtherSigned : {true, false})
          expectExact(
              [&](bool Corrupt) {
                const LogicSort Checked = bitVector(W, true);
                const LogicSort Operand = bitVector(Other, OtherSigned);
                std::vector<Expr> Facts;
                std::mt19937_64 Random(W + Other);
                const std::vector<APInt> Lefts = operandValues(W, Random);
                const std::vector<APInt> Rights = operandValues(Other, Random);
                for (const APInt &A : Lefts)
                  for (const APInt &B : Rights) {
                    // Operands are extended by their own signedness or
                    // truncated to W, then read as signed W-bit values.
                    APInt R = Other >= W
                                  ? B.trunc(W)
                                  : (OtherSigned ? B.sext(W) : B.zext(W));
                    const APInt WA = A.sext(2 * W + 2);
                    const APInt WR = R.sext(2 * W + 2);
                    APInt Exact(2 * W + 2, 0);
                    switch (C.Op) {
                    case LogicOverflowOp::Add:
                      Exact = WA + WR;
                      break;
                    case LogicOverflowOp::Sub:
                      Exact = WA - WR;
                      break;
                    case LogicOverflowOp::Mul:
                      Exact = WA * WR;
                      break;
                    case LogicOverflowOp::Neg:
                      Exact = -WA;
                      break;
                    case LogicOverflowOp::SignedDiv:
                      Exact =
                          (A.isMinSignedValue() && R.isAllOnes())
                              ? APInt::getSignedMaxValue(W).sext(2 * W + 2) + 1
                              : APInt(2 * W + 2, 0);
                      break;
                    }
                    bool Fits =
                        Exact.sge(
                            APInt::getSignedMinValue(W).sext(2 * W + 2)) &&
                        Exact.sle(APInt::getSignedMaxValue(W).sext(2 * W + 2));
                    if (Corrupt && Facts.empty())
                      Fits = !Fits;
                    Expr Check =
                        leaf(LogicExpr::NoOverflow, LogicSort::boolSort());
                    Check->OverflowOp = C.Op;
                    Check->Children.push_back(literal(A, Checked));
                    if (C.Op != LogicOverflowOp::Neg)
                      Check->Children.push_back(literal(B, Operand));
                    Facts.push_back(Fits ? std::move(Check)
                                         : node(LogicExpr::Not,
                                                LogicSort::boolSort(),
                                                std::move(Check)));
                    if (C.Op == LogicOverflowOp::Neg)
                      break;
                  }
                return conjunction(std::move(Facts));
              },
              std::string("overflow ") + C.Name + " i" + std::to_string(W) +
                  " with i" + std::to_string(Other) + (OtherSigned ? "s" : "u"),
              W == 8 && Other == W);
}

// One value per query: disjunctions of array round trips are slow on
// bit-vectors at 32 bits and above.
TEST(MachineIntegerEncodingTest, HeapCellRoundTrip) {
  const LogicSort Heap = LogicSort::heap();
  const LogicSort Pointer = LogicSort::pointer();
  for (unsigned W : {1u, 8u, 32u, 64u})
    for (bool Signed : {true, false})
      for (unsigned ReadWidth : {W, 8u, 64u})
        for (bool ReadSigned : {true, false}) {
          const LogicSort Sort = bitVector(W, Signed);
          const LogicSort Read = bitVector(ReadWidth, ReadSigned);
          std::vector<APInt> Values = {
              APInt(W, 0), APInt(W, 1), APInt::getAllOnes(W),
              APInt::getSignedMinValue(W), APInt::getSignedMaxValue(W)};
          for (const APInt &V : Values)
            expectExact(
                [&](bool Corrupt) {
                  APInt Bits =
                      ReadWidth >= W ? V.zext(ReadWidth) : V.trunc(ReadWidth);
                  if (Corrupt)
                    Bits += 1;
                  Expr Address = literal(APInt(64, 4096), Pointer);
                  Expr Store = node(LogicExpr::Store, LogicSort::boolSort(),
                                    variable("h0", Heap), clone(*Address),
                                    literal(V, Sort), variable("h1", Heap));
                  Expr Load = node(LogicExpr::Select, Read,
                                   variable("h1", Heap), std::move(Address));
                  return implies(std::move(Store),
                                 boolean(LogicExpr::Eq, std::move(Load),
                                         literal(Bits, Read)));
                },
                "heap i" + std::to_string(W) + (Signed ? "s" : "u") + " " +
                    decimal(V, Signed) + " read as i" +
                    std::to_string(ReadWidth) + (ReadSigned ? "s" : "u"),
                W == 8 && ReadWidth == 64);
        }
}

LogicFunctionDecl specDeclaration(const LogicSort &Sort, Expr Definition) {
  LogicFunctionDecl Decl;
  Decl.Identity = "f";
  Decl.DisplayName = "f";
  Decl.Parameters.push_back({"p", Sort});
  Decl.ResultSort = Sort;
  if (Definition) {
    Decl.DefinitionFuel = 1;
    Decl.StepDefinition = clone(*Definition);
    Decl.DefinitionLevels.push_back(std::move(Definition));
  }
  return Decl;
}

Expr specCall(const LogicSort &Sort, Expr Argument) {
  Expr Call = leaf(LogicExpr::SpecCall, Sort);
  Call->SpecCallee = "f";
  Call->Children.push_back(std::move(Argument));
  return Call;
}

// An opaque machine-sorted spec application must stay inside its sort's
// range; an unconstrained integer function would admit non-machine values.
TEST(MachineIntegerEncodingTest, OpaqueSpecResultsStayInRange) {
  for (unsigned W : {1u, 8u, 64u})
    for (bool Signed : {true, false}) {
      const LogicSort Sort = bitVector(W, Signed);
      const APInt Min = Signed ? APInt::getSignedMinValue(W) : APInt(W, 0);
      const APInt Max =
          Signed ? APInt::getSignedMaxValue(W) : APInt::getAllOnes(W);
      for (const Configuration &Config : configurations(true)) {
        std::map<std::string, LogicFunctionDecl> Functions;
        Functions.emplace("f", specDeclaration(Sort, nullptr));
        Expr InRange =
            boolean(LogicExpr::And,
                    boolean(LogicExpr::Le, literal(Min, Sort),
                            specCall(Sort, variable("x", Sort))),
                    boolean(LogicExpr::Le, specCall(Sort, variable("x", Sort)),
                            literal(Max, Sort)));
        VerifyResult Result =
            run(makeModule(std::move(InRange), std::move(Functions)), Config);
        EXPECT_EQ(Result.Status, VerifyStatus::Verified)
            << "opaque i" << W << (Signed ? "s" : "u") << " [" << Config.name()
            << "] " << statusName(Result.Status) << ": " << Result.Message;
      }
    }
}

// A defined machine-integer spec function is unfolded at its call sites.
TEST(MachineIntegerEncodingTest, DefinedSpecFunction) {
  for (unsigned W : {3u, 8u, 64u})
    for (bool Signed : {true, false}) {
      const LogicSort Sort = bitVector(W, Signed);
      auto definition = [&] {
        return node(LogicExpr::Add, Sort,
                    node(LogicExpr::Mul, Sort, variable("p", Sort),
                         literal(APInt(W, 3), Sort)),
                    literal(APInt(W, 1), Sort));
      };
      for (const Configuration &Config : configurations(true))
        for (bool Corrupt : {false, true}) {
          std::vector<Expr> Facts;
          forEachValue(W, [&](const APInt &V) {
            APInt Expected = V * 3 + 1;
            if (Corrupt && Facts.empty())
              Expected += 1;
            Facts.push_back(boolean(LogicExpr::Eq,
                                    specCall(Sort, literal(V, Sort)),
                                    literal(Expected, Sort)));
          });
          std::map<std::string, LogicFunctionDecl> Functions;
          Functions.emplace("f", specDeclaration(Sort, definition()));
          VerifyResult Result = run(
              makeModule(conjunction(std::move(Facts)), std::move(Functions)),
              Config);
          EXPECT_EQ(Result.Status,
                    Corrupt ? VerifyStatus::Failed : VerifyStatus::Verified)
              << "spec i" << W << (Signed ? "s" : "u")
              << (Corrupt ? " corrupted" : "") << " [" << Config.name() << "] "
              << statusName(Result.Status) << ": " << Result.Message;
        }
    }
}

// Counterexamples must report source-level machine values in both encodings.
TEST(MachineIntegerEncodingTest, CounterexampleValuesAreMachineValues) {
  for (bool Signed : {true, false}) {
    const LogicSort Sort = bitVector(8, Signed);
    const APInt Boundary =
        Signed ? APInt::getSignedMaxValue(8) : APInt::getAllOnes(8);
    // x + 1 never wraps: false exactly at the type's maximum.
    Expr Goal = boolean(LogicExpr::Gt,
                        node(LogicExpr::Add, Sort, variable("x", Sort),
                             literal(APInt(8, 1), Sort)),
                        variable("x", Sort));
    for (const Configuration &Config : configurations(false)) {
      VerifyResult Result = run(makeModule(clone(*Goal)), Config);
      ASSERT_EQ(Result.Status, VerifyStatus::Failed) << Config.name();
      ASSERT_EQ(Result.Model.size(), 1u) << Config.name();
      EXPECT_EQ(Result.Model.front().Value, decimal(Boundary, Signed))
          << Config.name();
    }
  }
}

const LogicSort Math = LogicSort::mathematicalInteger(64, true);

Expr forall(llvm::StringRef Binder, uint64_t Lo, uint64_t Hi, Expr Body) {
  Expr Quantifier = node(LogicExpr::Forall, LogicSort::boolSort(),
                         mathLiteral(APInt(64, Lo), false),
                         mathLiteral(APInt(64, Hi), false), std::move(Body));
  Quantifier->Binder = Binder.str();
  return Quantifier;
}

Expr binderBits(const LogicSort &Sort) {
  return node(LogicExpr::IntToBv, Sort, variable("i", Math));
}

// Forced integers keep int2bv under a binder and may stay unresolved; auto
// must decide.
TEST(MachineIntegerEncodingTest, QuantifiedBitLevelOperations) {
  const Encodings All = {MachineIntegerEncoding::Auto,
                         MachineIntegerEncoding::Integer,
                         MachineIntegerEncoding::BitVector};
  const Tolerance IntegerOrCVC5 = [](const Configuration &Config) {
    return Config.Encoding == MachineIntegerEncoding::Integer ||
           Config.Solver == BackendKind::CVC5;
  };
  for (unsigned W : {8u, 32u, 64u})
    for (bool Signed : {true, false}) {
      const LogicSort Sort = bitVector(W, Signed);
      // (i | x) & i == i for every x; the corrupted goal claims x instead.
      expectExact(
          [&](bool Corrupt) {
            Expr Absorbed = node(LogicExpr::BitAnd, Sort,
                                 node(LogicExpr::BitOr, Sort, binderBits(Sort),
                                      variable("x", Sort)),
                                 binderBits(Sort));
            return forall(
                "i", 0, 16,
                boolean(LogicExpr::Eq, std::move(Absorbed),
                        Corrupt ? variable("x", Sort) : binderBits(Sort)));
          },
          "absorption under forall i" + std::to_string(W) +
              (Signed ? "s" : "u"),
          W == 8, All, IntegerOrCVC5);
    }
  for (unsigned W : {8u, 32u, 64u}) {
    const LogicSort Sort = bitVector(W, false);
    // x >> i <= x for unsigned x; the corrupted goal claims <.
    expectExact(
        [&](bool Corrupt) {
          Expr Shifted =
              node(LogicExpr::Shr, Sort, variable("x", Sort), binderBits(Sort));
          return forall("i", 0, W,
                        boolean(Corrupt ? LogicExpr::Lt : LogicExpr::Le,
                                std::move(Shifted), variable("x", Sort)));
        },
        "shift under forall u" + std::to_string(W), W == 8, All, IntegerOrCVC5);
  }
}

MachineIntegerEncoding z3Encoding(const ObligationModule &M,
                                  MachineIntegerEncoding Requested,
                                  std::string *Dump) {
  Z3Encoder Encoder;
  Encoder.setIntegerEncoding(Requested);
  std::string Text;
  llvm::raw_string_ostream OS(Text);
  VerifyResult Lowered = Encoder.lowerModule(M, &OS);
  EXPECT_EQ(Lowered.Status, VerifyStatus::Lowered) << Lowered.Message;
  if (Dump)
    *Dump = OS.str();
  return Encoder.activeIntegerEncoding();
}

MachineIntegerEncoding z3AutoChoice(const ObligationModule &M) {
  return z3Encoding(M, MachineIntegerEncoding::Auto);
}

bool cvc5AutoUsesBitVectors(const ObligationModule &M) {
  auto Script = encodeSMTLibQuery(M, M.CounterexampleQuery.get(),
                                  MachineIntegerEncoding::Auto);
  if (!Script) {
    ADD_FAILURE() << llvm::toString(Script.takeError());
    return false;
  }
  return llvm::StringRef(*Script).contains("(_ BitVec");
}

// Auto keeps the integer encoding unless the query needs the bits of a
// non-constant operand: masks and constant shifts are arithmetic.
TEST(MachineIntegerEncodingTest, AutoResolution) {
  const LogicSort Sort = bitVector(32, false);
  auto x = [&] { return variable("x", Sort); };
  auto y = [&] { return variable("y", Sort); };
  auto lit = [&](uint64_t Value) { return literal(APInt(32, Value), Sort); };
  struct Case {
    const char *Name;
    std::function<Expr()> Goal;
    bool ExpectBitVectors;
  };
  const Case Cases[] = {
      {"ground and",
       [&] {
         return boolean(LogicExpr::Eq, node(LogicExpr::BitAnd, Sort, x(), y()),
                        node(LogicExpr::BitAnd, Sort, y(), x()));
       },
       true},
      {"ground symbolic shift",
       [&] {
         return boolean(LogicExpr::Le, node(LogicExpr::Shr, Sort, x(), y()),
                        x());
       },
       true},
      {"constant operands",
       [&] {
         return boolean(LogicExpr::Eq,
                        node(LogicExpr::BitOr, Sort, x(),
                             node(LogicExpr::BitAnd, Sort, lit(6), lit(3))),
                        node(LogicExpr::BitOr, Sort, x(), lit(2)));
       },
       true},
      {"mask and constant shift",
       [&] {
         return boolean(LogicExpr::Le,
                        node(LogicExpr::Shr, Sort,
                             node(LogicExpr::BitAnd, Sort, x(), lit(127)),
                             node(LogicExpr::Mul, Sort, lit(7), lit(0))),
                        lit(127));
       },
       false},
      {"mask under binder",
       [&] {
         return forall(
             "i", 0, 16,
             boolean(LogicExpr::Eq,
                     node(LogicExpr::BitAnd, Sort, binderBits(Sort), lit(255)),
                     binderBits(Sort)));
       },
       false},
      {"constant shift under binder",
       [&] {
         return forall(
             "i", 0, 16,
             boolean(LogicExpr::Le,
                     node(LogicExpr::Shr, Sort, binderBits(Sort), lit(1)),
                     binderBits(Sort)));
       },
       false},
      {"binder-dependent and",
       [&] {
         return forall(
             "i", 0, 16,
             boolean(LogicExpr::Le,
                     node(LogicExpr::BitAnd, Sort, binderBits(Sort), x()),
                     binderBits(Sort)));
       },
       true},
      {"binder-dependent shift amount",
       [&] {
         return forall(
             "i", 0, 16,
             boolean(LogicExpr::Le,
                     node(LogicExpr::Shr, Sort, x(), binderBits(Sort)), x()));
       },
       true},
  };
  for (const Case &C : Cases) {
    ObligationModule M = makeModule(C.Goal());
    EXPECT_EQ(z3AutoChoice(M), C.ExpectBitVectors
                                   ? MachineIntegerEncoding::BitVector
                                   : MachineIntegerEncoding::Integer)
        << C.Name;
    EXPECT_EQ(cvc5AutoUsesBitVectors(M), C.ExpectBitVectors) << C.Name;
    for (const Configuration &Config :
         configurations(true, {MachineIntegerEncoding::Auto})) {
      VerifyResult Result = run(M, Config);
      if (Config.Solver == BackendKind::CVC5 &&
          Result.Status == VerifyStatus::Unresolved)
        continue;
      EXPECT_EQ(Result.Status, VerifyStatus::Verified)
          << C.Name << " [" << Config.name() << "] " << Result.Message;
    }
  }
}

// The integer encoding names the bits of a ground operand by a bit-vector
// defined through bv2int, and keeps int2bv only under a quantifier binder.
TEST(MachineIntegerEncodingTest, IntegerBitLevelOperands) {
  const LogicSort Sort = bitVector(32, true);
  std::string Ground;
  z3Encoding(
      makeModule(boolean(LogicExpr::Eq,
                         node(LogicExpr::BitAnd, Sort, variable("x", Sort),
                              variable("y", Sort)),
                         node(LogicExpr::BitAnd, Sort, variable("y", Sort),
                              variable("x", Sort)))),
      MachineIntegerEncoding::Integer, &Ground);
  EXPECT_TRUE(llvm::StringRef(Ground).contains("bits!0")) << Ground;
  EXPECT_FALSE(llvm::StringRef(Ground).contains("int2bv")) << Ground;
  std::string Quantified;
  z3Encoding(
      makeModule(forall("i", 0, 16,
                        boolean(LogicExpr::Le,
                                node(LogicExpr::BitAnd, Sort, binderBits(Sort),
                                     variable("x", Sort)),
                                binderBits(Sort)))),
      MachineIntegerEncoding::Integer, &Quantified);
  EXPECT_TRUE(llvm::StringRef(Quantified).contains("int2bv")) << Quantified;
}

// Range facts must not turn irrelevant variables into reported values.
TEST(MachineIntegerEncodingTest, IrrelevantVariablesStayUnknown) {
  const LogicSort Sort = bitVector(32, true);
  const LogicSort Bool = LogicSort::boolSort();
  // Fails exactly when !take and z > 5, whatever x and y are.
  Expr Goal = boolean(
      LogicExpr::Or,
      boolean(
          LogicExpr::Or, variable("take", Bool),
          node(LogicExpr::Ite, Bool, variable("take", Bool),
               boolean(LogicExpr::Eq, variable("x", Sort), variable("y", Sort)),
               leaf(LogicExpr::False, Bool))),
      boolean(LogicExpr::Le, variable("z", Sort), literal(APInt(32, 5), Sort)));
  for (const Configuration &Config :
       configurations(false, {MachineIntegerEncoding::Auto,
                              MachineIntegerEncoding::Integer,
                              MachineIntegerEncoding::BitVector})) {
    VerifyResult Result = run(makeModule(clone(*Goal)), Config);
    ASSERT_EQ(Result.Status, VerifyStatus::Failed) << Config.name();
    std::map<std::string, std::optional<std::string>> Values;
    for (const VerifyModelValue &Value : Result.Model)
      Values[Value.InternalName] = Value.Value;
    EXPECT_EQ(Values["take"], std::optional<std::string>("false"))
        << Config.name();
    ASSERT_TRUE(Values["z"].has_value()) << Config.name();
    EXPECT_GT(std::stoll(*Values["z"]), 5) << Config.name();
    EXPECT_FALSE(Values["x"].has_value()) << Config.name() << " x";
    EXPECT_FALSE(Values["y"].has_value()) << Config.name() << " y";
  }
}

} // namespace
