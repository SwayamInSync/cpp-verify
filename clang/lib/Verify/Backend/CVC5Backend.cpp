//===--- CVC5Backend.cpp --------------------------------------------------===//
#include "CVC5Backend.h"
#include "Certify.h"
#include "ObligationSerialization.h"
#include "ObligationSimplify.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/STLFunctionalExtras.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/FileUtilities.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/Program.h"
#include "llvm/Support/ThreadPool.h"
#include "llvm/Support/Threading.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>
#include <chrono>
#include <limits>
#include <map>
#include <mutex>
#include <optional>
#include <set>
#include <thread>

#if defined(_WIN32)
#include "llvm/Support/Windows/WindowsSupport.h"
#else
#include <cerrno>
#include <csignal>
#include <sys/wait.h>
#endif

using namespace clang;
using namespace verify;

namespace {

constexpr uint64_t MaxSolverOutputBytes = 64 * 1024;
/// A satisfiable check prints its model after the verdict.
constexpr uint64_t MaxModelOutputBytes = 16 * 1024 * 1024;
/// Least time cvc5 gets for refinement rounds, and how many of them may only
/// search among hidden functions' values.
constexpr unsigned RefinementShareMs = 2000;
constexpr unsigned HiddenSearchRounds = 32;

std::string outputLimitText(uint64_t Bytes) {
  return Bytes >= 1024 * 1024 ? std::to_string(Bytes / (1024 * 1024)) + " MiB"
                              : std::to_string(Bytes / 1024) + " KiB";
}

static std::string smtSymbol(llvm::StringRef Prefix, llvm::StringRef Identity) {
  static constexpr char Hex[] = "0123456789abcdef";
  std::string Result = Prefix.str();
  Result.reserve(Result.size() + Identity.size() * 2);
  for (unsigned char Byte : Identity.bytes()) {
    Result.push_back(Hex[Byte >> 4]);
    Result.push_back(Hex[Byte & 0x0f]);
  }
  return Result;
}

static std::string smtInteger(llvm::StringRef Value) {
  if (!Value.consume_front("-"))
    return Value.str();
  return "(- " + Value.str() + ")";
}

static std::string decimalUnsigned(const llvm::APInt &Value) {
  llvm::SmallString<128> Buffer;
  Value.toString(Buffer, 10, false);
  return std::string(Buffer);
}

static std::string decimalPowerOfTwo(unsigned Exponent) {
  llvm::APInt Value(Exponent + 1, 1);
  Value <<= Exponent;
  llvm::SmallString<128> Buffer;
  Value.toString(Buffer, 10, false);
  return std::string(Buffer);
}

class SMTLibEncoder {
  const ObligationModule &Module;
  const MachineIntegerEncoding Encoding;
  std::map<std::string, LogicSort> FreeVariables;
  std::map<std::string, const LogicFunctionDecl *> UsedFunctions;
  std::vector<std::map<std::string, std::string>> BoundScopes;
  /// What a binder's range proves about its values, innermost last.
  struct BinderBounds {
    std::string Binder;
    std::optional<llvm::APInt> Lo;
    std::optional<llvm::APInt> HiLiteral;
    std::optional<LogicSort> HiSort;
  };
  std::vector<BinderBounds> Bounds;
  std::map<std::string, std::string> Substitutions;
  std::vector<std::string> Axioms;
  std::string Definitions;
  std::set<std::string> NonRecursive;
  uint64_t LocalIndex = 0;
  bool UsesValidPtr = false;
  /// Sequence operations under quantifiers need enumerative instantiation.
  bool UsesSequences = false;
  bool UsesQuantifiers = false;
  /// Maps hold cppverify.option values; set union, intersection, and
  /// difference are functions defined pointwise by an axiom each.
  bool UsesMaps = false;
  std::set<std::string> SetOperations;
  bool UsedBitLevelOperation = false;
  bool Failed = false;
  std::string Error;

  void fail(llvm::Twine Message) {
    if (Failed)
      return;
    Failed = true;
    Error = Message.str();
  }

  std::string freshLocal(llvm::StringRef Prefix) {
    return (Prefix + llvm::Twine(LocalIndex++)).str();
  }

  std::string sort(const LogicSort &Sort) {
    switch (Sort.Kind) {
    case LogicSortKind::Bool:
      return "Bool";
    case LogicSortKind::MathematicalInteger:
    case LogicSortKind::Pointer:
      return "Int";
    case LogicSortKind::BitVector:
      if (integerMode())
        return "Int";
      return "(_ BitVec " + std::to_string(Sort.BitWidth) + ")";
    case LogicSortKind::Heap:
      return "(Array Int Int)";
    case LogicSortKind::Seq:
      return "(Seq Int)";
    // Collections over all integers are arrays, as for Z3; cvc5's set
    // theory is finite.
    case LogicSortKind::Set:
      return "(Array Int Bool)";
    case LogicSortKind::Multiset:
      return "(Array Int Int)";
    case LogicSortKind::Map:
      UsesMaps = true;
      return "(Array Int cppverify.option)";
    case LogicSortKind::Invalid:
      fail("cannot encode an invalid logic sort");
      return "Bool";
    }
    fail("cannot encode an unknown logic sort");
    return "Bool";
  }

  static std::optional<llvm::APInt> integerLiteral(const LogicExpr *Expr) {
    if (!Expr || Expr->K != LogicExpr::IntLit ||
        Expr->Sort.Kind != LogicSortKind::MathematicalInteger)
      return std::nullopt;
    llvm::StringRef Digits(Expr->IntVal);
    if (Digits.empty() || Digits.size() > 30)
      return std::nullopt;
    return llvm::APInt(130, Digits, 10);
  }

  /// Whether every value of \p Binder fits \p Sort, so that converting it
  /// to \p Sort is the identity.
  bool binderFits(llvm::StringRef Binder, const LogicSort &Sort) const {
    if (Sort.Kind != LogicSortKind::BitVector || Sort.BitWidth == 0 ||
        Sort.BitWidth > 128)
      return false;
    for (auto It = Bounds.rbegin(); It != Bounds.rend(); ++It) {
      if (It->Binder != Binder)
        continue;
      const bool Signed = isSignedSort(Sort);
      const llvm::APInt Min =
          Signed ? -llvm::APInt::getOneBitSet(130, Sort.BitWidth - 1)
                 : llvm::APInt(130, 0);
      const llvm::APInt End = llvm::APInt::getOneBitSet(
          130, Signed ? Sort.BitWidth - 1 : Sort.BitWidth);
      if (!It->Lo || It->Lo->slt(Min))
        return false;
      if (It->HiLiteral)
        return It->HiLiteral->sle(End);
      if (!It->HiSort)
        return false;
      const LogicSort &From = *It->HiSort;
      if (isSignedSort(From) == Signed)
        return From.BitWidth <= Sort.BitWidth;
      return isSignedSort(From) && From.BitWidth <= Sort.BitWidth;
    }
    return false;
  }

  std::string boundVariable(llvm::StringRef Name) const {
    for (auto Scope = BoundScopes.rbegin(); Scope != BoundScopes.rend();
         ++Scope) {
      auto It = Scope->find(Name.str());
      if (It != Scope->end())
        return It->second;
    }
    return {};
  }

  std::string freeVariable(llvm::StringRef Name, const LogicSort &Sort) {
    auto [It, Inserted] = FreeVariables.emplace(Name.str(), Sort);
    const bool Equivalent = It->second.Kind == Sort.Kind &&
                            (Sort.Kind == LogicSortKind::MathematicalInteger ||
                             (It->second.BitWidth == Sort.BitWidth &&
                              It->second.Signedness == Sort.Signedness));
    if (!Inserted && !Equivalent)
      fail("logical variable has inconsistent SMT-LIB sorts: " + Name);
    return smtSymbol("v_", Name);
  }

  std::string functionName(const LogicFunctionDecl &Function) {
    UsedFunctions.emplace(Function.Identity, &Function);
    return smtSymbol("f_", Function.Identity);
  }

  static bool isIntegerSort(const LogicSort &Sort) {
    return Sort.Kind == LogicSortKind::MathematicalInteger ||
           Sort.Kind == LogicSortKind::Pointer;
  }

  std::string intToBV(llvm::StringRef Value, unsigned Width) {
    return "((_ int2bv " + std::to_string(Width) + ") " + Value.str() + ")";
  }

  std::string unsignedBVToInt(llvm::StringRef Value) {
    return "(bv2nat " + Value.str() + ")";
  }

  std::string signedBVToInt(llvm::StringRef Value, unsigned Width) {
    const std::string Local = freshLocal("sbv_");
    return "(let ((" + Local + " " + Value.str() + ")) (ite (= ((_ extract " +
           std::to_string(Width - 1) + " " + std::to_string(Width - 1) + ") " +
           Local + ") #b1) (- (bv2nat " + Local + ") " +
           decimalPowerOfTwo(Width) + ") (bv2nat " + Local + ")))";
  }

  std::string resizeBV(llvm::StringRef Value, const LogicSort &Source,
                       unsigned TargetWidth) {
    if (Source.Kind != LogicSortKind::BitVector || Source.BitWidth == 0 ||
        TargetWidth == 0) {
      fail("cannot resize a non-bitvector SMT-LIB term");
      return "(_ bv0 1)";
    }
    if (Source.BitWidth == TargetWidth)
      return Value.str();
    if (Source.BitWidth < TargetWidth) {
      const char *Op = Source.Signedness == LogicSignedness::Signed
                           ? "sign_extend"
                           : "zero_extend";
      return "((_ " + std::string(Op) + " " +
             std::to_string(TargetWidth - Source.BitWidth) + ") " +
             Value.str() + ")";
    }
    return "((_ extract " + std::to_string(TargetWidth - 1) + " 0) " +
           Value.str() + ")";
  }

  std::string coerce(llvm::StringRef Value, const LogicSort &Source,
                     const LogicSort &Target, bool IsSigned) {
    if (integerMode()) {
      if (Target.Kind == LogicSortKind::BitVector) {
        if (Source.Kind == LogicSortKind::BitVector) {
          if (Source.BitWidth != Target.BitWidth) {
            fail("bit-vector coercion changes width");
            return "false";
          }
          return reinterpret(Value, Target.BitWidth, isSignedSort(Source),
                             isSignedSort(Target));
        }
        if (isIntegerSort(Source))
          return reduce(Value, Target);
        fail("unsupported SMT-LIB sort coercion");
        return "false";
      }
      if (isIntegerSort(Target) && Source.Kind == LogicSortKind::BitVector)
        return reinterpret(Value, Source.BitWidth, isSignedSort(Source),
                           IsSigned);
      if (Source.Kind == Target.Kind ||
          (isIntegerSort(Source) && isIntegerSort(Target)))
        return Value.str();
      fail("unsupported SMT-LIB sort coercion");
      return "false";
    }
    if (Source.Kind == Target.Kind) {
      if (Source.Kind != LogicSortKind::BitVector ||
          Source.BitWidth == Target.BitWidth)
        return Value.str();
    }
    if (isIntegerSort(Source) && isIntegerSort(Target))
      return Value.str();
    if (isIntegerSort(Source) && Target.Kind == LogicSortKind::BitVector)
      return intToBV(Value, Target.BitWidth);
    if (Source.Kind == LogicSortKind::BitVector && isIntegerSort(Target))
      return IsSigned ? signedBVToInt(Value, Source.BitWidth)
                      : unsignedBVToInt(Value);
    fail("unsupported SMT-LIB sort coercion");
    return "false";
  }

  std::string mathDivision(llvm::StringRef Left, llvm::StringRef Right) {
    const std::string L = freshLocal("div_l_");
    const std::string R = freshLocal("div_r_");
    const std::string Magnitude = "(div (ite (< " + L + " 0) (- " + L + ") " +
                                  L + ") (ite (< " + R + " 0) (- " + R + ") " +
                                  R + "))";
    const std::string Signed = "(ite (xor (< " + L + " 0) (< " + R +
                               " 0)) (- " + Magnitude + ") " + Magnitude + ")";
    return "(let ((" + L + " " + Left.str() + ") (" + R + " " + Right.str() +
           ")) (ite (= " + R + " 0) 0 " + Signed + "))";
  }

  std::string mathRemainder(llvm::StringRef Left, llvm::StringRef Right) {
    const std::string L = freshLocal("rem_l_");
    const std::string R = freshLocal("rem_r_");
    const std::string Q = freshLocal("rem_q_");
    const std::string Quotient = mathDivision(L, R);
    return "(let ((" + L + " " + Left.str() + ") (" + R + " " + Right.str() +
           ")) (let ((" + Q + " " + Quotient + ")) (ite (= " + R + " 0) " + L +
           " (- " + L + " (* " + Q + " " + R + ")))))";
  }

  bool integerMode() const {
    return Encoding == MachineIntegerEncoding::Integer;
  }

  static bool isSignedSort(const LogicSort &Sort) {
    return Sort.Signedness == LogicSignedness::Signed;
  }

  /// Bit pattern of a constant machine-integer term.
  static std::optional<llvm::APInt> machineConstant(const LogicExpr *Expr) {
    if (!Expr || Expr->Sort.Kind != LogicSortKind::BitVector ||
        Expr->Sort.BitWidth == 0)
      return std::nullopt;
    const unsigned Width = Expr->Sort.BitWidth;
    auto parse = [Width](llvm::StringRef Decimal) {
      const unsigned Parsed = std::max<unsigned>(
          Width, static_cast<unsigned>(Decimal.size()) * 4 + 2);
      return llvm::APInt(Parsed, Decimal, 10).trunc(Width);
    };
    if (Expr->K == LogicExpr::IntLit)
      return parse(Expr->IntVal);
    if (Expr->Children.empty() || Expr->Children.size() > 2)
      return std::nullopt;
    const LogicExpr *Inner = Expr->Children[0].get();
    if (Expr->K == LogicExpr::IntToBv)
      return Inner->K == LogicExpr::IntLit
                 ? std::optional<llvm::APInt>(parse(Inner->IntVal))
                 : std::nullopt;
    std::optional<llvm::APInt> L = machineConstant(Inner);
    if (!L)
      return std::nullopt;
    if (Expr->K == LogicExpr::BvResize)
      return isSignedSort(Inner->Sort) ? L->sextOrTrunc(Width)
                                       : L->zextOrTrunc(Width);
    if (L->getBitWidth() != Width)
      return std::nullopt;
    if (Expr->Children.size() == 1) {
      if (Expr->K == LogicExpr::Neg)
        return -*L;
      if (Expr->K == LogicExpr::BitNot)
        return ~*L;
      return std::nullopt;
    }
    std::optional<llvm::APInt> R = machineConstant(Expr->Children[1].get());
    if (!R || R->getBitWidth() != Width)
      return std::nullopt;
    switch (Expr->K) {
    case LogicExpr::Add:
      return *L + *R;
    case LogicExpr::Sub:
      return *L - *R;
    case LogicExpr::Mul:
      return *L * *R;
    case LogicExpr::BitAnd:
      return *L & *R;
    case LogicExpr::BitOr:
      return *L | *R;
    case LogicExpr::BitXor:
      return *L ^ *R;
    case LogicExpr::Shl:
      return R->uge(Width) ? llvm::APInt(Width, 0)
                           : L->shl(static_cast<unsigned>(R->getZExtValue()));
    case LogicExpr::Shr:
      if (!isSignedSort(Expr->Sort))
        return R->uge(Width)
                   ? llvm::APInt(Width, 0)
                   : L->lshr(static_cast<unsigned>(R->getZExtValue()));
      return L->ashr(static_cast<unsigned>(
          std::min<uint64_t>(R->getLimitedValue(), Width - 1)));
    default:
      return std::nullopt;
    }
  }

  std::string machineLiteral(const llvm::APInt &Bits, const LogicSort &Sort) {
    llvm::SmallString<64> Canonical;
    Bits.toString(Canonical, 10, isSignedSort(Sort));
    return smtInteger(Canonical);
  }

  std::string letBind(llvm::StringRef Value, llvm::StringRef Prefix,
                      llvm::function_ref<std::string(llvm::StringRef)> Body) {
    const std::string Local = freshLocal(Prefix);
    return "(let ((" + Local + " " + Value.str() + ")) " + Body(Local) + ")";
  }

  std::string machineLiteral(llvm::StringRef Decimal, const LogicSort &Sort) {
    const unsigned Parsed = std::max<unsigned>(
        Sort.BitWidth, static_cast<unsigned>(Decimal.size()) * 4 + 2);
    return machineLiteral(llvm::APInt(Parsed, Decimal, 10).trunc(Sort.BitWidth),
                          Sort);
  }

  std::string reduce(llvm::StringRef Value, const LogicSort &Sort) {
    const std::string Modulus = decimalPowerOfTwo(Sort.BitWidth);
    if (!isSignedSort(Sort))
      return "(mod " + Value.str() + " " + Modulus + ")";
    const std::string Half = decimalPowerOfTwo(Sort.BitWidth - 1);
    return "(- (mod (+ " + Value.str() + " " + Half + ") " + Modulus + ") " +
           Half + ")";
  }

  std::string inRangeOf(llvm::StringRef V, const LogicSort &Sort) {
    if (!isSignedSort(Sort))
      return "(and (<= 0 " + V.str() + ") (< " + V.str() + " " +
             decimalPowerOfTwo(Sort.BitWidth) + "))";
    const std::string Half = decimalPowerOfTwo(Sort.BitWidth - 1);
    return "(and (<= (- " + Half + ") " + V.str() + ") (< " + V.str() + " " +
           Half + "))";
  }

  std::string inRange(llvm::StringRef Value, const LogicSort &Sort) {
    return letBind(Value, "rng_",
                   [&](llvm::StringRef V) { return inRangeOf(V, Sort); });
  }

  std::string reinterpret(llvm::StringRef Value, unsigned Width,
                          bool FromSigned, bool ToSigned) {
    if (FromSigned == ToSigned)
      return Value.str();
    const std::string Modulus = decimalPowerOfTwo(Width);
    return letBind(Value, "re_", [&](llvm::StringRef V) {
      if (FromSigned)
        return "(ite (< " + V.str() + " 0) (+ " + V.str() + " " + Modulus +
               ") " + V.str() + ")";
      return "(ite (>= " + V.str() + " " + decimalPowerOfTwo(Width - 1) +
             ") (- " + V.str() + " " + Modulus + ") " + V.str() + ")";
    });
  }

  std::string convertMachine(llvm::StringRef Value, const LogicSort &Source,
                             const LogicSort &Target) {
    const bool FromSigned = isSignedSort(Source);
    const bool ToSigned = isSignedSort(Target);
    if (Target.BitWidth == Source.BitWidth)
      return reinterpret(Value, Target.BitWidth, FromSigned, ToSigned);
    if (Target.BitWidth < Source.BitWidth)
      return reduce(Value, Target);
    if (FromSigned && !ToSigned)
      return letBind(Value, "ext_", [&](llvm::StringRef V) {
        return "(ite (< " + V.str() + " 0) (+ " + V.str() + " " +
               decimalPowerOfTwo(Target.BitWidth) + ") " + V.str() + ")";
      });
    return Value.str();
  }

  std::string truncatingDivision(llvm::StringRef Left, llvm::StringRef Right) {
    const std::string L = freshLocal("tdiv_l_");
    const std::string R = freshLocal("tdiv_r_");
    const std::string Magnitude = "(div (abs " + L + ") (abs " + R + "))";
    return "(let ((" + L + " " + Left.str() + ") (" + R + " " + Right.str() +
           ")) (ite (= (>= " + L + " 0) (>= " + R + " 0)) " + Magnitude +
           " (- " + Magnitude + ")))";
  }

  std::string integerArithmetic(const LogicExpr *Expr, llvm::StringRef Left,
                                llvm::StringRef Right) {
    if (std::optional<llvm::APInt> Bits = machineConstant(Expr))
      return machineLiteral(*Bits, Expr->Sort);
    const LogicSort &Sort = Expr->Children[0]->Sort;
    const unsigned Width = Sort.BitWidth;
    const bool Signed = isSignedSort(Sort);
    auto toBits = [&](unsigned Index, llvm::StringRef Value) {
      if (std::optional<llvm::APInt> Bits =
              machineConstant(Expr->Children[Index].get()))
        return "(_ bv" + decimalUnsigned(Bits->zextOrTrunc(Width)) + " " +
               std::to_string(Width) + ")";
      UsedBitLevelOperation = true;
      return intToBV(Value, Width);
    };
    auto fromBits = [&](llvm::StringRef Bits) {
      return Signed ? signedBVToInt(Bits, Width) : unsignedBVToInt(Bits);
    };
    auto literal = [&](unsigned Index) -> std::optional<llvm::APInt> {
      std::optional<llvm::APInt> Bits =
          machineConstant(Expr->Children[Index].get());
      if (!Bits)
        return std::nullopt;
      return Bits->zextOrTrunc(Width);
    };
    switch (Expr->K) {
    case LogicExpr::Add:
      return reduce("(+ " + Left.str() + " " + Right.str() + ")", Sort);
    case LogicExpr::Sub:
      return reduce("(- " + Left.str() + " " + Right.str() + ")", Sort);
    case LogicExpr::Mul:
      return reduce("(* " + Left.str() + " " + Right.str() + ")", Sort);
    case LogicExpr::Div: {
      const std::string L = freshLocal("idiv_l_");
      const std::string R = freshLocal("idiv_r_");
      const std::string Bind = "(let ((" + L + " " + Left.str() + ") (" + R +
                               " " + Right.str() + ")) ";
      if (Signed)
        return Bind + "(ite (= " + R + " 0) (ite (>= " + L + " 0) (- 1) " +
               machineLiteral("1", Sort) + ") " +
               reduce(truncatingDivision(L, R), Sort) + "))";
      return Bind + "(ite (= " + R + " 0) (- " + decimalPowerOfTwo(Width) +
             " 1) (div " + L + " " + R + ")))";
    }
    case LogicExpr::Rem: {
      const std::string L = freshLocal("irem_l_");
      const std::string R = freshLocal("irem_r_");
      const std::string Bind = "(let ((" + L + " " + Left.str() + ") (" + R +
                               " " + Right.str() + ")) ";
      if (Signed)
        return Bind + "(ite (= " + R + " 0) " + L + " (- " + L + " (* " + R +
               " " + truncatingDivision(L, R) + "))))";
      return Bind + "(ite (= " + R + " 0) " + L + " (mod " + L + " " + R +
             ")))";
    }
    case LogicExpr::BitAnd: {
      // x & (2^k - 1) keeps the low k bits: x mod 2^k in either range.
      for (auto [MaskIndex, Value] :
           {std::pair{1u, Left}, std::pair{0u, Right}}) {
        std::optional<llvm::APInt> Mask = literal(MaskIndex);
        if (!Mask || (Signed && Mask->isNegative()))
          continue;
        llvm::APInt Wide = Mask->zext(Width + 1);
        if ((Wide + 1).isPowerOf2())
          return "(mod " + Value.str() + " " +
                 decimalPowerOfTwo((Wide + 1).logBase2()) + ")";
      }
      return fromBits("(bvand " + toBits(0, Left) + " " + toBits(1, Right) +
                      ")");
    }
    case LogicExpr::BitOr:
      return fromBits("(bvor " + toBits(0, Left) + " " + toBits(1, Right) +
                      ")");
    case LogicExpr::BitXor:
      return fromBits("(bvxor " + toBits(0, Left) + " " + toBits(1, Right) +
                      ")");
    case LogicExpr::Shl:
    case LogicExpr::Shr: {
      std::optional<llvm::APInt> Amount = literal(1);
      if (!Amount) {
        const char *Op = Expr->K == LogicExpr::Shl ? "bvshl"
                         : Signed                  ? "bvashr"
                                                   : "bvlshr";
        return fromBits("(" + std::string(Op) + " " + toBits(0, Left) + " " +
                        toBits(1, Right) + ")");
      }
      if (Amount->uge(Width)) {
        if (Expr->K == LogicExpr::Shl || !Signed)
          return "0";
        return "(ite (< " + Left.str() + " 0) (- 1) 0)";
      }
      const std::string Scale =
          decimalPowerOfTwo(static_cast<unsigned>(Amount->getZExtValue()));
      if (Expr->K == LogicExpr::Shl)
        return reduce("(* " + Left.str() + " " + Scale + ")", Sort);
      return "(div " + Left.str() + " " + Scale + ")";
    }
    default:
      fail("unsupported SMT-LIB machine-integer operator");
      return "0";
    }
  }

  std::string integerOverflowCheck(const LogicExpr *Expr) {
    const LogicSort Checked =
        LogicSort::bitVector(Expr->Children[0]->Sort.BitWidth, true);
    std::vector<std::string> Operands;
    for (const auto &Child : Expr->Children)
      Operands.push_back(
          convertMachine(encode(Child.get()), Child->Sort, Checked));
    if (Expr->OverflowOp == LogicOverflowOp::Neg)
      return inRange("(- " + Operands[0] + ")", Checked);
    if (Operands.size() != 2) {
      fail("binary SMT-LIB overflow predicate is missing an operand");
      return "false";
    }
    switch (Expr->OverflowOp) {
    case LogicOverflowOp::Add:
      return inRange("(+ " + Operands[0] + " " + Operands[1] + ")", Checked);
    case LogicOverflowOp::Sub:
      return inRange("(- " + Operands[0] + " " + Operands[1] + ")", Checked);
    case LogicOverflowOp::Mul:
      return inRange("(* " + Operands[0] + " " + Operands[1] + ")", Checked);
    case LogicOverflowOp::SignedDiv:
      return "(not (and (= " + Operands[0] + " (- " +
             decimalPowerOfTwo(Checked.BitWidth - 1) + ")) (= " + Operands[1] +
             " (- 1))))";
    case LogicOverflowOp::Neg:
      llvm_unreachable("handled above");
    }
    llvm_unreachable("unknown overflow operation");
  }

  /// Pure bit-vector arithmetic: the exact result of sign-extended operands
  /// fits the signed range. Mixing in integer conversions leaves cvc5 unknown.
  std::string overflowCheck(const LogicExpr *Expr) {
    if (Expr->Children.empty() ||
        Expr->Children[0]->Sort.Kind != LogicSortKind::BitVector) {
      fail("malformed SMT-LIB overflow predicate");
      return "false";
    }
    const unsigned Width = Expr->Children[0]->Sort.BitWidth;
    std::vector<std::string> Operands;
    for (const auto &Child : Expr->Children) {
      std::string Value = encode(Child.get());
      Operands.push_back(resizeBV(Value, Child->Sort, Width));
    }
    auto constant = [](const llvm::APInt &Value, unsigned ToWidth) {
      return "(_ bv" + decimalUnsigned(Value.sext(ToWidth)) + " " +
             std::to_string(ToWidth) + ")";
    };
    auto inRange = [&](const std::string &Value, unsigned ToWidth) {
      return "(and (bvsle " +
             constant(llvm::APInt::getSignedMinValue(Width), ToWidth) + " " +
             Value + ") (bvsle " + Value + " " +
             constant(llvm::APInt::getSignedMaxValue(Width), ToWidth) + "))";
    };
    auto extend = [](const std::string &Value, unsigned By) {
      return "((_ sign_extend " + std::to_string(By) + ") " + Value + ")";
    };
    if (Expr->OverflowOp == LogicOverflowOp::Neg)
      return inRange("(bvneg " + extend(Operands[0], 1) + ")", Width + 1);
    if (Operands.size() != 2) {
      fail("binary SMT-LIB overflow predicate is missing an operand");
      return "false";
    }
    switch (Expr->OverflowOp) {
    case LogicOverflowOp::Add:
      return inRange("(bvadd " + extend(Operands[0], 1) + " " +
                         extend(Operands[1], 1) + ")",
                     Width + 1);
    case LogicOverflowOp::Sub:
      return inRange("(bvsub " + extend(Operands[0], 1) + " " +
                         extend(Operands[1], 1) + ")",
                     Width + 1);
    case LogicOverflowOp::Mul:
      return inRange("(bvmul " + extend(Operands[0], Width) + " " +
                         extend(Operands[1], Width) + ")",
                     2 * Width);
    case LogicOverflowOp::SignedDiv:
      return "(not (and (= " + Operands[0] + " " +
             constant(llvm::APInt::getSignedMinValue(Width), Width) +
             ") (= " + Operands[1] + " " +
             constant(llvm::APInt::getAllOnes(Width), Width) + ")))";
    case LogicOverflowOp::Neg:
      llvm_unreachable("handled above");
    }
    llvm_unreachable("unknown overflow operation");
  }

  std::string encode(const LogicExpr *Expr) {
    if (!Expr) {
      fail("cannot encode a null SMT-LIB term");
      return "false";
    }
    auto Child = [&](unsigned Index) {
      if (Index >= Expr->Children.size()) {
        fail("SMT-LIB term has insufficient operands");
        return std::string("false");
      }
      return encode(Expr->Children[Index].get());
    };
    switch (Expr->K) {
    case LogicExpr::True:
      return "true";
    case LogicExpr::False:
      return "false";
    case LogicExpr::BoolLit:
      return Expr->BoolVal ? "true" : "false";
    case LogicExpr::IntLit:
      if (Expr->Sort.Kind == LogicSortKind::BitVector)
        return integerMode()
                   ? machineLiteral(Expr->IntVal, Expr->Sort)
                   : intToBV(smtInteger(Expr->IntVal), Expr->Sort.BitWidth);
      return smtInteger(Expr->IntVal);
    case LogicExpr::Var: {
      if (std::string Bound = boundVariable(Expr->Name); !Bound.empty())
        return Bound;
      if (auto It = Substitutions.find(Expr->Name); It != Substitutions.end())
        return It->second;
      return freeVariable(Expr->Name, Expr->Sort);
    }
    case LogicExpr::Not:
      return "(not " + Child(0) + ")";
    case LogicExpr::And:
    case LogicExpr::Or: {
      std::string Result = Expr->K == LogicExpr::And ? "(and" : "(or";
      for (const auto &Operand : Expr->Children)
        Result += " " + encode(Operand.get());
      return Result + ")";
    }
    case LogicExpr::Ite:
      return "(ite " + Child(0) + " " + Child(1) + " " + Child(2) + ")";
    case LogicExpr::Eq:
      return equality(Expr, Child(0), Child(1));
    case LogicExpr::Ne:
      return "(not " + equality(Expr, Child(0), Child(1)) + ")";
    case LogicExpr::Lt:
    case LogicExpr::Le:
    case LogicExpr::Gt:
    case LogicExpr::Ge: {
      const LogicSort &OperandSort = Expr->Children[0]->Sort;
      const bool Signed = OperandSort.Signedness == LogicSignedness::Signed;
      const char *Op = nullptr;
      if (OperandSort.Kind == LogicSortKind::BitVector && !integerMode()) {
        switch (Expr->K) {
        case LogicExpr::Lt:
          Op = Signed ? "bvslt" : "bvult";
          break;
        case LogicExpr::Le:
          Op = Signed ? "bvsle" : "bvule";
          break;
        case LogicExpr::Gt:
          Op = Signed ? "bvsgt" : "bvugt";
          break;
        case LogicExpr::Ge:
          Op = Signed ? "bvsge" : "bvuge";
          break;
        default:
          llvm_unreachable("not a comparison");
        }
      } else {
        switch (Expr->K) {
        case LogicExpr::Lt:
          Op = "<";
          break;
        case LogicExpr::Le:
          Op = "<=";
          break;
        case LogicExpr::Gt:
          Op = ">";
          break;
        case LogicExpr::Ge:
          Op = ">=";
          break;
        default:
          llvm_unreachable("not a comparison");
        }
      }
      return "(" + std::string(Op) + " " + Child(0) + " " + Child(1) + ")";
    }
    case LogicExpr::Add:
    case LogicExpr::Sub:
    case LogicExpr::Mul:
    case LogicExpr::Div:
    case LogicExpr::Rem:
    case LogicExpr::BitAnd:
    case LogicExpr::BitOr:
    case LogicExpr::BitXor:
    case LogicExpr::Shl:
    case LogicExpr::Shr: {
      std::string Left = Child(0);
      std::string Right = Child(1);
      if (integerMode() && Expr->Sort.Kind == LogicSortKind::BitVector)
        return integerArithmetic(Expr, Left, Right);
      if (Expr->Sort.Kind != LogicSortKind::BitVector) {
        if (Expr->K == LogicExpr::Div)
          return mathDivision(Left, Right);
        if (Expr->K == LogicExpr::Rem)
          return mathRemainder(Left, Right);
      }
      const bool Signed = Expr->Sort.Signedness == LogicSignedness::Signed;
      const char *Op = nullptr;
      switch (Expr->K) {
      case LogicExpr::Add:
        Op = Expr->Sort.Kind == LogicSortKind::BitVector ? "bvadd" : "+";
        break;
      case LogicExpr::Sub:
        Op = Expr->Sort.Kind == LogicSortKind::BitVector ? "bvsub" : "-";
        break;
      case LogicExpr::Mul:
        Op = Expr->Sort.Kind == LogicSortKind::BitVector ? "bvmul" : "*";
        break;
      case LogicExpr::Div:
        Op = Signed ? "bvsdiv" : "bvudiv";
        break;
      case LogicExpr::Rem:
        Op = Signed ? "bvsrem" : "bvurem";
        break;
      case LogicExpr::BitAnd:
        Op = "bvand";
        break;
      case LogicExpr::BitOr:
        Op = "bvor";
        break;
      case LogicExpr::BitXor:
        Op = "bvxor";
        break;
      case LogicExpr::Shl:
        Op = "bvshl";
        break;
      case LogicExpr::Shr:
        Op = Signed ? "bvashr" : "bvlshr";
        break;
      default:
        llvm_unreachable("not a binary arithmetic term");
      }
      return "(" + std::string(Op) + " " + Left + " " + Right + ")";
    }
    case LogicExpr::Neg: {
      if (integerMode())
        if (std::optional<llvm::APInt> Bits = machineConstant(Expr))
          return machineLiteral(*Bits, Expr->Sort);
      std::string Value = Child(0);
      if (integerMode() && Expr->Sort.Kind == LogicSortKind::BitVector)
        return reduce("(- " + Value + ")", Expr->Sort);
      return Expr->Sort.Kind == LogicSortKind::BitVector
                 ? "(bvneg " + Value + ")"
                 : "(- " + Value + ")";
    }
    case LogicExpr::BitNot:
      // ~x is -x - 1 on two's-complement bits, which stays in either range.
      if (integerMode()) {
        if (std::optional<llvm::APInt> Bits = machineConstant(Expr))
          return machineLiteral(*Bits, Expr->Sort);
        return isSignedSort(Expr->Sort)
                   ? "(- (- " + Child(0) + ") 1)"
                   : "(- (- " + decimalPowerOfTwo(Expr->Sort.BitWidth) +
                         " 1) " + Child(0) + ")";
      }
      return "(bvnot " + Child(0) + ")";
    case LogicExpr::ValidPtr:
      UsesValidPtr = true;
      return "(p_valid " + Child(0) + ")";
    case LogicExpr::Select: {
      const std::string Cell = "(select " + Child(0) + " " + Child(1) + ")";
      if (Expr->Sort.Kind == LogicSortKind::Bool)
        return "(not (= " + Cell + " 0))";
      if (Expr->Sort.Kind == LogicSortKind::BitVector)
        return integerMode() ? reduce(Cell, Expr->Sort)
                             : intToBV(Cell, Expr->Sort.BitWidth);
      return Cell;
    }
    case LogicExpr::Store: {
      std::string Value = Child(2);
      const LogicSort &ValueSort = Expr->Children[2]->Sort;
      if (ValueSort.Kind == LogicSortKind::Bool)
        Value = "(ite " + Value + " 1 0)";
      else if (ValueSort.Kind == LogicSortKind::BitVector)
        Value = integerMode() ? reinterpret(Value, ValueSort.BitWidth,
                                            isSignedSort(ValueSort), false)
                              : unsignedBVToInt(Value);
      return "(= " + Child(3) + " (store " + Child(0) + " " + Child(1) + " " +
             Value + "))";
    }
    case LogicExpr::Collection:
      return collection(Expr);
    case LogicExpr::HeapFrame: {
      UsesQuantifiers = true;
      const std::string Address = "frame_address";
      std::string Inside = "false";
      for (unsigned I = 2; I + 1 < Expr->Children.size(); I += 2)
        Inside = "(or " + Inside + " (and (<= " + Child(I) + " " + Address +
                 ") (< " + Address + " " + Child(I + 1) + ")))";
      return "(forall ((" + Address + " Int)) (or " + Inside + " (= (select " +
             Child(1) + " " + Address + ") (select " + Child(0) + " " +
             Address + "))))";
    }
    case LogicExpr::Forall:
    case LogicExpr::Exists: {
      UsesQuantifiers = true;
      if (Expr->Children.size() == 1) {
        const std::string Binder = smtSymbol(
            ("q" + std::to_string(BoundScopes.size()) + "_").c_str(),
            Expr->Binder);
        BoundScopes.push_back({{Expr->Binder, Binder}});
        const std::string Body = withPattern(Expr, Child(0));
        BoundScopes.pop_back();
        return std::string(Expr->K == LogicExpr::Forall ? "(forall"
                                                        : "(exists") +
               " ((" + Binder + " Int)) " + Body + ")";
      }
      const std::string Lower = Child(0);
      const std::string Upper = Child(1);
      const std::string Binder =
          smtSymbol(("q" + std::to_string(BoundScopes.size()) + "_").c_str(),
                    Expr->Binder);
      BoundScopes.push_back({{Expr->Binder, Binder}});
      BinderBounds Known;
      Known.Binder = Expr->Binder;
      Known.Lo = integerLiteral(Expr->Children[0].get());
      Known.HiLiteral = integerLiteral(Expr->Children[1].get());
      if (Expr->Children[1]->K == LogicExpr::BvToInt &&
          Expr->Children[1]->Children.size() == 1)
        Known.HiSort = Expr->Children[1]->Children[0]->Sort;
      Bounds.push_back(std::move(Known));
      const std::string Body = Child(2);
      const std::string Range = "(and (<= " + Lower + " " + Binder + ") (< " +
                                Binder + " " + Upper + "))";
      const std::string Quantified =
          Expr->K == LogicExpr::Forall
              ? withPattern(Expr, "(=> " + Range + " " + Body + ")")
              : withPattern(Expr, "(and " + Range + " " + Body + ")");
      Bounds.pop_back();
      BoundScopes.pop_back();
      return std::string(Expr->K == LogicExpr::Forall ? "(forall"
                                                      : "(exists") +
             " ((" + Binder + " Int)) " + Quantified + ")";
    }
    case LogicExpr::IntToBv:
      if (integerMode()) {
        if (std::optional<llvm::APInt> Bits = machineConstant(Expr))
          return machineLiteral(*Bits, Expr->Sort);
        // A binder whose range fits the sort converts to itself; the reduced
        // form would hide it from instantiation.
        if (Expr->Children[0]->K == LogicExpr::Var &&
            !boundVariable(Expr->Children[0]->Name).empty() &&
            binderFits(Expr->Children[0]->Name, Expr->Sort))
          return Child(0);
        return reduce(Child(0), Expr->Sort);
      }
      return intToBV(Child(0), Expr->Sort.BitWidth);
    case LogicExpr::BvToInt: {
      // The canonical integer already is the value under its signedness.
      if (integerMode())
        return Child(0);
      const LogicSort &Source = Expr->Children[0]->Sort;
      return Source.Signedness == LogicSignedness::Signed
                 ? signedBVToInt(Child(0), Source.BitWidth)
                 : unsignedBVToInt(Child(0));
    }
    case LogicExpr::BvResize:
      if (integerMode()) {
        if (std::optional<llvm::APInt> Bits = machineConstant(Expr))
          return machineLiteral(*Bits, Expr->Sort);
        return convertMachine(Child(0), Expr->Children[0]->Sort, Expr->Sort);
      }
      return resizeBV(Child(0), Expr->Children[0]->Sort, Expr->Sort.BitWidth);
    case LogicExpr::NoOverflow:
      if (integerMode()) {
        if (Expr->Children.empty() ||
            Expr->Children[0]->Sort.Kind != LogicSortKind::BitVector) {
          fail("malformed SMT-LIB overflow predicate");
          return "false";
        }
        return integerOverflowCheck(Expr);
      }
      return overflowCheck(Expr);
    case LogicExpr::SpecCall: {
      const LogicFunctionDecl *Found = declaration(Expr->SpecCallee);
      if (!Found) {
        fail("missing SMT-LIB spec declaration: " + Expr->SpecCallee);
        return "false";
      }
      const LogicFunctionDecl &Function = *Found;
      std::string Application = functionName(Function);
      if (!Expr->Children.empty())
        Application = "(" + Application;
      for (unsigned I = 0; I != Expr->Children.size(); ++I) {
        std::string Argument = Child(I);
        Argument = coerce(
            Argument, Expr->Children[I]->Sort, Function.Parameters[I].Sort,
            Function.Parameters[I].Sort.Signedness == LogicSignedness::Signed);
        Application += " " + Argument;
      }
      if (!Expr->Children.empty())
        Application += ")";
      // Keep an opaque machine-sorted application in range, as in Z3.
      if (integerMode() && Function.ResultSort.Kind == LogicSortKind::BitVector)
        Application = reduce(Application, Function.ResultSort);
      return coerce(Application, Function.ResultSort, Expr->Sort,
                    Function.ResultSort.Signedness == LogicSignedness::Signed);
    }
    }
    fail("unsupported SMT-LIB expression");
    return "false";
  }

  /// A collection operation, with cppverify.h's total semantics.
  std::string collection(const LogicExpr *Expr) {
    if (isSequenceOperation(Expr->CollectionOp))
      UsesSequences = true;
    std::vector<std::string> A;
    for (const auto &Child : Expr->Children)
      A.push_back(encode(Child.get()));
    auto arg = [&](size_t I) -> std::string {
      if (I < A.size())
        return A[I];
      fail("collection operation lacks an operand");
      return "0";
    };
    auto len = [](const std::string &S) { return "(seq.len " + S + ")"; };
    auto unit = [](const std::string &X) { return "(seq.unit " + X + ")"; };
    auto extract = [](const std::string &S, const std::string &From,
                      const std::string &Count) {
      return "(seq.extract " + S + " " + From + " " + Count + ")";
    };
    using Op = LogicCollectionOp;
    switch (Expr->CollectionOp) {
    case Op::SeqEmpty:
      return "(as seq.empty (Seq Int))";
    case Op::SeqUnit:
      return unit(arg(0));
    case Op::SeqLength:
      return len(arg(0));
    case Op::SeqIndex:
      return "(ite (and (<= 0 " + arg(1) + ") (< " + arg(1) + " " +
             len(arg(0)) + ")) (seq.nth " + arg(0) + " " + arg(1) + ") 0)";
    case Op::SeqPush:
      return "(seq.++ " + arg(0) + " " + unit(arg(1)) + ")";
    case Op::SeqSubrange: {
      // seq.extract clamps by itself; only a negative start differs.
      const std::string S = arg(0), Lo = arg(1), Hi = arg(2);
      const std::string FromLo = extract(S, Lo, "(- " + Hi + " " + Lo + ")");
      const LogicExpr *Start =
          Expr->Children.size() > 1 ? Expr->Children[1].get() : nullptr;
      if (Start && Start->K == LogicExpr::IntLit &&
          !llvm::StringRef(Start->IntVal).starts_with("-"))
        return FromLo;
      return "(ite (< " + Lo + " 0) " + extract(S, "0", Hi) + " " + FromLo +
             ")";
    }
    case Op::SeqConcat:
      return "(seq.++ " + arg(0) + " " + arg(1) + ")";
    case Op::SeqContains:
      return "(seq.contains " + arg(0) + " " + unit(arg(1)) + ")";
    case Op::SetEmpty:
      return "((as const (Array Int Bool)) false)";
    case Op::SetInsert:
      return "(store " + arg(0) + " " + arg(1) + " true)";
    case Op::SetRemove:
      return "(store " + arg(0) + " " + arg(1) + " false)";
    case Op::SetContains:
      return "(select " + arg(0) + " " + arg(1) + ")";
    case Op::SetUnion:
    case Op::SetIntersect:
    case Op::SetDifference: {
      const std::string Name =
          Expr->CollectionOp == Op::SetUnion       ? "cppverify.set_union"
          : Expr->CollectionOp == Op::SetIntersect ? "cppverify.set_intersect"
                                                   : "cppverify.set_difference";
      SetOperations.insert(Name);
      return "(" + Name + " " + arg(0) + " " + arg(1) + ")";
    }
    case Op::SetSubset: {
      const std::string K = freshLocal("subset");
      UsesQuantifiers = true;
      return "(forall ((" + K + " Int)) (=> (select " + arg(0) + " " + K +
             ") (select " + arg(1) + " " + K + ")))";
    }
    case Op::MultisetEmpty:
      return "((as const (Array Int Int)) 0)";
    case Op::MultisetInsert:
      return "(store " + arg(0) + " " + arg(1) + " (+ " +
             count(arg(0), arg(1)) + " 1))";
    case Op::MultisetRemove: {
      const std::string C = count(arg(0), arg(1));
      return "(store " + arg(0) + " " + arg(1) + " (ite (> " + C + " 0) (- " +
             C + " 1) 0))";
    }
    case Op::MultisetCount:
      return count(arg(0), arg(1));
    case Op::MapEmpty:
      UsesMaps = true;
      return "((as const (Array Int cppverify.option)) cppverify.none)";
    case Op::MapInsert:
      UsesMaps = true;
      return "(store " + arg(0) + " " + arg(1) + " (cppverify.some " + arg(2) +
             "))";
    case Op::MapRemove:
      UsesMaps = true;
      return "(store " + arg(0) + " " + arg(1) + " cppverify.none)";
    case Op::MapContains:
      UsesMaps = true;
      return "((_ is cppverify.some) (select " + arg(0) + " " + arg(1) + "))";
    case Op::MapGet: {
      UsesMaps = true;
      const std::string Cell = "(select " + arg(0) + " " + arg(1) + ")";
      return "(ite ((_ is cppverify.some) " + Cell + ") (cppverify.value " +
             Cell + ") 0)";
    }
    default:
      fail("unsupported collection operation for cvc5");
      return "false";
    }
  }

  /// Equality as cppverify.h defines it: multisets agree count by count,
  /// since a cell below zero counts zero.
  std::string equality(const LogicExpr *Expr, const std::string &Left,
                       const std::string &Right) {
    if (Expr->Children[0]->Sort.Kind != LogicSortKind::Multiset)
      return "(= " + Left + " " + Right + ")";
    UsesQuantifiers = true;
    const std::string E = freshLocal("element");
    return "(forall ((" + E + " Int)) (= " + count(Left, E) + " " +
           count(Right, E) + "))";
  }

  /// A multiset count: a cell below zero counts as none.
  static std::string count(const std::string &Multiset,
                           const std::string &Element) {
    const std::string Cell = "(select " + Multiset + " " + Element + ")";
    return "(ite (>= " + Cell + " 0) " + Cell + " 0)";
  }

  static bool isSequenceOperation(LogicCollectionOp Op) {
    switch (Op) {
    case LogicCollectionOp::SeqEmpty:
    case LogicCollectionOp::SeqUnit:
    case LogicCollectionOp::SeqLength:
    case LogicCollectionOp::SeqIndex:
    case LogicCollectionOp::SeqPush:
    case LogicCollectionOp::SeqSubrange:
    case LogicCollectionOp::SeqConcat:
    case LogicCollectionOp::SeqContains:
      return true;
    default:
      return false;
    }
  }

  /// Body annotated with the quantifier's trigger when every term is a heap
  /// select; cvc5 chooses triggers itself otherwise.
  std::string withPattern(const LogicExpr *Quantifier, std::string Body) {
    if (Quantifier->Patterns.empty())
      return Body;
    std::string Terms;
    for (const auto &Pattern : Quantifier->Patterns) {
      if (Pattern->K != LogicExpr::Select || Pattern->Children.size() != 2)
        return Body;
      Terms += " (select " + encode(Pattern->Children[0].get()) + " " +
               encode(Pattern->Children[1].get()) + ")";
    }
    return "(! " + Body + " :pattern (" + Terms.substr(1) + "))";
  }

  static void collectSpecCalls(const LogicExpr *Expr,
                               std::vector<const LogicExpr *> &Calls) {
    if (!Expr)
      return;
    if (Expr->K == LogicExpr::SpecCall)
      Calls.push_back(Expr);
    for (const auto &Child : Expr->Children)
      collectSpecCalls(Child.get(), Calls);
  }

  void emitSpecAxiom(const LogicExpr *Call) {
    auto It = Module.LogicFunctions.find(Call->SpecCallee);
    if (It == Module.LogicFunctions.end()) {
      fail("missing SMT-LIB spec definition: " + Call->SpecCallee);
      return;
    }
    const LogicFunctionDecl &Function = It->second;
    if (Function.DefinitionLevels.empty())
      return;
    std::vector<std::string> Arguments;
    for (unsigned I = 0; I != Call->Children.size(); ++I) {
      std::string Argument = encode(Call->Children[I].get());
      Arguments.push_back(coerce(
          Argument, Call->Children[I]->Sort, Function.Parameters[I].Sort,
          Function.Parameters[I].Sort.Signedness == LogicSignedness::Signed));
    }
    std::string Left = functionName(Function);
    if (!Arguments.empty())
      Left = "(" + Left;
    for (const std::string &Argument : Arguments)
      Left += " " + Argument;
    if (!Arguments.empty())
      Left += ")";

    std::vector<std::pair<std::string, std::optional<std::string>>> Saved;
    for (unsigned I = 0; I != Function.Parameters.size(); ++I) {
      const std::string &Name = Function.Parameters[I].Name;
      auto Existing = Substitutions.find(Name);
      Saved.emplace_back(Name,
                         Existing == Substitutions.end()
                             ? std::optional<std::string>()
                             : std::optional<std::string>(Existing->second));
      Substitutions[Name] = Arguments[I];
    }
    for (const auto &Definition : Function.DefinitionLevels) {
      std::string Right = encode(Definition.get());
      Right = coerce(Right, Definition->Sort, Function.ResultSort,
                     Function.ResultSort.Signedness == LogicSignedness::Signed);
      Axioms.push_back("(assert (= " + Left + " " + Right + "))");
    }
    for (const auto &[Name, Value] : Saved) {
      if (Value)
        Substitutions[Name] = *Value;
      else
        Substitutions.erase(Name);
    }
  }

  std::string literal(const LogicValue &Value, const LogicSort &Sort) {
    switch (Value.K) {
    case LogicValue::Kind::Bool:
      return Value.Truth ? "true" : "false";
    case LogicValue::Kind::Heap: {
      // Runs become stores, cell by cell, up to a bound; a longer run keeps
      // only its first cell, which still names a true instance argument.
      std::string Heap = "((as const (Array Int Int)) " +
                         smtInteger(Value.Heap->Default.toDecimal()) + ")";
      const auto &Breaks = Value.Heap->Breaks;
      unsigned Budget = 4096;
      for (auto It = Breaks.begin(); It != Breaks.end(); ++It) {
        if (It->second == Value.Heap->Default)
          continue;
        auto Next = std::next(It);
        CertInt Address = It->first;
        do {
          Heap = "(store " + Heap + " " + smtInteger(Address.toDecimal()) +
                 " " + smtInteger(It->second.toDecimal()) + ")";
          Address = Address + CertInt(1);
        } while (Budget-- > 0 && Next != Breaks.end() &&
                 Address < Next->first);
      }
      return Heap;
    }
    case LogicValue::Kind::Integer:
      if (Sort.Kind == LogicSortKind::BitVector && !integerMode())
        return "(_ bv" + decimalUnsigned(Value.Integer.bits(Sort.BitWidth)) +
               " " + std::to_string(Sort.BitWidth) + ")";
      return smtInteger(Value.Integer.toDecimal());
    case LogicValue::Kind::Seq: {
      const std::vector<CertInt> &Elements = *Value.Elements;
      if (Elements.empty())
        return "(as seq.empty (Seq Int))";
      std::string Units;
      for (const CertInt &Element : Elements)
        Units += " (seq.unit " + smtInteger(Element.toDecimal()) + ")";
      return Elements.size() == 1 ? Units.substr(1) : "(seq.++" + Units + ")";
    }
    case LogicValue::Kind::Set:
    case LogicValue::Kind::Multiset:
    case LogicValue::Kind::Map:
      break;
    }
    fail("unsupported SMT-LIB literal");
    return "false";
  }

  std::vector<const LogicFunctionDecl *>
  callees(const LogicFunctionDecl &Function) const {
    std::vector<const LogicExpr *> Calls;
    collectSpecCalls(Function.StepDefinition.get(), Calls);
    std::vector<const LogicFunctionDecl *> Callees;
    for (const LogicExpr *Call : Calls)
      if (auto It = Module.LogicFunctions.find(Call->SpecCallee);
          It != Module.LogicFunctions.end())
        Callees.push_back(&It->second);
    return Callees;
  }

  /// define-fun for \p Function, after the functions its definition applies.
  /// cvc5 does not decide queries over define-fun-rec, so a recursive
  /// function stays declared.
  void define(const LogicFunctionDecl &Function) {
    if (Defined.count(Function.Identity) ||
        !NonRecursive.count(Function.Identity))
      return;
    Defined.insert(Function.Identity);
    for (const LogicFunctionDecl *Callee : callees(Function))
      define(*Callee);
    std::string Text = "(define-fun " + functionName(Function) + " (";
    std::map<std::string, std::string> Saved = Substitutions;
    for (unsigned I = 0; I != Function.Parameters.size(); ++I) {
      const std::string Parameter = "arg_" + std::to_string(I);
      Text += "(" + Parameter + " " + sort(Function.Parameters[I].Sort) + ")";
      Substitutions[Function.Parameters[I].Name] = Parameter;
    }
    Text += ") " + sort(Function.ResultSort) + " " +
            coerce(encode(Function.StepDefinition.get()),
                   Function.StepDefinition->Sort, Function.ResultSort,
                   Function.ResultSort.Signedness == LogicSignedness::Signed) +
            ")\n";
    Substitutions = std::move(Saved);
    Definitions += Text;
  }

  /// A declared function of the module, or one only the facts of a
  /// counterexample check apply.
  const LogicFunctionDecl *declaration(const std::string &Identity) const {
    if (auto It = Module.LogicFunctions.find(Identity);
        It != Module.LogicFunctions.end())
      return &It->second;
    if (auto It = Module.EvidenceFunctions.find(Identity);
        It != Module.EvidenceFunctions.end())
      return &It->second;
    return nullptr;
  }

  /// A true fact at one application: f(args) = definition[args], an
  /// inductive predicate's unfolding, or proved postconditions.
  void emitDefinitionInstance(const DefinitionInstance &Instance) {
    const LogicFunctionDecl &Function = *Instance.Function;
    using Kind = DefinitionInstance::Kind;
    const LogicExpr *Body = Instance.Of == Kind::Unfolding
                                ? Function.Unfolding.get()
                                : Function.StepDefinition.get();
    if ((Instance.Of != Kind::Postcondition && !Body) ||
        (Instance.Of == Kind::Postcondition &&
         Function.Postconditions.empty()) ||
        Instance.Arguments.size() != Function.Parameters.size()) {
      fail("definition instance of " + Function.DisplayName +
           " cannot be encoded");
      return;
    }
    std::vector<std::string> Arguments;
    for (unsigned I = 0; I != Instance.Arguments.size(); ++I)
      Arguments.push_back(
          literal(Instance.Arguments[I], Function.Parameters[I].Sort));
    std::string Left = functionName(Function);
    if (!Arguments.empty()) {
      Left = "(" + Left;
      for (const std::string &Argument : Arguments)
        Left += " " + Argument;
      Left += ")";
    }
    std::map<std::string, std::string> Saved = Substitutions;
    for (unsigned I = 0; I != Function.Parameters.size(); ++I)
      Substitutions[Function.Parameters[I].Name] = Arguments[I];
    if (Instance.Of == Kind::Postcondition) {
      Substitutions[LogicFunctionDecl::ResultVariable] = Left;
      std::string Holds = "true";
      for (const auto &Post : Function.Postconditions)
        Holds = "(and " + Holds + " " + encode(Post.get()) + ")";
      Substitutions = std::move(Saved);
      Axioms.push_back("(assert " + Holds + ")");
      return;
    }
    std::string Right =
        coerce(encode(Body), Body->Sort, Function.ResultSort,
               Function.ResultSort.Signedness == LogicSignedness::Signed);
    Substitutions = std::move(Saved);
    Axioms.push_back("(assert (= " + Left + " " + Right + "))");
  }

public:
  SMTLibEncoder(const ObligationModule &Module, MachineIntegerEncoding Encoding)
      : Module(Module), Encoding(Encoding) {}

  bool usedBitLevelOperation() const { return UsedBitLevelOperation; }
  std::vector<DefinitionInstance> Instances;
  /// Quantifiers whose range, and applications whose integer arguments, the
  /// solver is asked to keep small.
  std::vector<const LogicExpr *> Narrowed;
  /// Define every non-recursive logical function, hidden ones included,
  /// instead of declaring it. Only for a search whose unsat proves nothing.
  bool DefineFunctions = false;
  std::set<std::string> Defined;

  llvm::Expected<std::string> run(const LogicExpr *Query) {
    if (!Query)
      return llvm::createStringError(llvm::inconvertibleErrorCode(),
                                     "missing SMT-LIB counterexample query");
    std::unique_ptr<LogicExpr> Instantiated = instantiateAtReads(*Query);
    if (Instantiated)
      Query = Instantiated.get();
    std::vector<const LogicExpr *> Calls;
    collectSpecCalls(Query, Calls);
    for (const LogicExpr *Call : Calls)
      emitSpecAxiom(Call);
    for (const DefinitionInstance &Instance : Instances)
      emitDefinitionInstance(Instance);
    for (const LogicExpr *Narrow : Narrowed) {
      if (Narrow->K == LogicExpr::Forall || Narrow->K == LogicExpr::Exists) {
        Axioms.push_back("(assert (<= (- " +
                         encode(Narrow->Children[1].get()) + " " +
                         encode(Narrow->Children[0].get()) + ") " +
                         std::to_string(NarrowedQuantifierRange) + "))");
        continue;
      }
      const std::string Bound = std::to_string(NarrowedArgumentBound);
      for (const auto &Argument : Narrow->Children) {
        const LogicSort &Sort = Argument->Sort;
        const std::string Value = encode(Argument.get());
        if (Sort.Kind == LogicSortKind::MathematicalInteger ||
            (Sort.Kind == LogicSortKind::BitVector && integerMode())) {
          Axioms.push_back("(assert (and (<= " + Value + " " + Bound +
                           ") (>= " + Value + " (- " + Bound + "))))");
        } else if (Sort.Kind == LogicSortKind::BitVector &&
                   Sort.BitWidth > 13) {
          const std::string Width = std::to_string(Sort.BitWidth);
          const std::string Upper = "((_ int2bv " + Width + ") " + Bound + ")";
          if (Sort.Signedness == LogicSignedness::Signed)
            Axioms.push_back("(assert (and (bvsle " + Value + " " + Upper +
                             ") (bvsge " + Value + " ((_ int2bv " + Width +
                             ") (- " + Bound + ")))))");
          else
            Axioms.push_back("(assert (bvule " + Value + " " + Upper + "))");
        }
      }
    }
    const std::string EncodedQuery = encode(Query);
    if (DefineFunctions) {
      NonRecursive = nonRecursiveDefinitions(Module);
    } else {
      // A visible non-recursive definition is exact and finite: define it
      // whole, so an application under a quantifier is interpreted too.
      for (const std::string &Identity : nonRecursiveDefinitions(Module))
        if (auto It = Module.LogicFunctions.find(Identity);
            It != Module.LogicFunctions.end() && It->second.DefinitionFuel > 0)
          NonRecursive.insert(Identity);
    }
    const std::map<std::string, const LogicFunctionDecl *> Used = UsedFunctions;
    for (const auto &[Identity, Function] : Used)
      define(*Function);
    if (Failed)
      return llvm::createStringError(llvm::inconvertibleErrorCode(), "%s",
                                     Error.c_str());

    std::string Script;
    llvm::raw_string_ostream Out(Script);
    Out << "(set-logic ALL)\n";
    Out << "(set-option :print-success false)\n";
    // Without it, cvc5 gives up on quantified sequence goals that E-matching
    // does not close.
    if (UsesSequences && UsesQuantifiers)
      Out << "(set-option :full-saturate-quant true)\n";
    for (const auto &[Name, VariableSort] : FreeVariables)
      UsesMaps |= VariableSort.Kind == LogicSortKind::Map;
    for (const auto &[Identity, Function] : UsedFunctions) {
      UsesMaps |= Function->ResultSort.Kind == LogicSortKind::Map;
      for (const LogicFunctionParameter &Parameter : Function->Parameters)
        UsesMaps |= Parameter.Sort.Kind == LogicSortKind::Map;
    }
    if (UsesMaps)
      Out << "(declare-datatype cppverify.option ((cppverify.none) "
             "(cppverify.some (cppverify.value Int))))\n";
    // Each set operation is the function its pointwise axiom defines, by
    // extensionality of arrays.
    for (const std::string &Name : SetOperations) {
      const char *Cell = Name == "cppverify.set_union"
                             ? "(or (select a k) (select b k))"
                         : Name == "cppverify.set_intersect"
                             ? "(and (select a k) (select b k))"
                             : "(and (select a k) (not (select b k)))";
      Out << "(declare-fun " << Name
          << " ((Array Int Bool) (Array Int Bool)) (Array Int Bool))\n"
          << "(assert (forall ((a (Array Int Bool)) (b (Array Int Bool)) "
             "(k Int)) (! (= (select ("
          << Name << " a b) k) " << Cell << ") :pattern ((select (" << Name
          << " a b) k)))))\n";
    }
    for (const auto &[Name, VariableSort] : FreeVariables)
      Out << "(declare-fun " << smtSymbol("v_", Name) << " () "
          << sort(VariableSort) << ")\n";
    if (integerMode())
      for (const auto &[Name, VariableSort] : FreeVariables)
        if (VariableSort.Kind == LogicSortKind::BitVector)
          Out << "(assert " << inRange(smtSymbol("v_", Name), VariableSort)
              << ")\n";
    if (UsesValidPtr)
      Out << "(declare-fun p_valid (Int) Bool)\n";
    for (const auto &[Identity, Function] : UsedFunctions) {
      if (Defined.count(Identity))
        continue;
      Out << "(declare-fun " << smtSymbol("f_", Function->Identity) << " (";
      for (unsigned I = 0; I != Function->Parameters.size(); ++I) {
        if (I != 0)
          Out << " ";
        Out << sort(Function->Parameters[I].Sort);
      }
      Out << ") " << sort(Function->ResultSort) << ")\n";
    }
    Out << Definitions;
    for (const std::string &Axiom : Axioms)
      Out << Axiom << "\n";
    Out << "(assert " << EncodedQuery << ")\n";
    Out << "(check-sat)\n";
    Out << "(exit)\n";
    Out.flush();
    if (Failed)
      return llvm::createStringError(llvm::inconvertibleErrorCode(), "%s",
                                     Error.c_str());
    return Script;
  }
};

static VerifyResult querySizeLimitResult(const ObligationModule &Module,
                                         uint64_t MaxQueryNodes,
                                         llvm::StringRef BackendName) {
  VerifyResult Result;
  if (MaxQueryNodes == 0 || obligationModuleNodeCount(Module) <= MaxQueryNodes)
    return Result;
  Result.Status = VerifyStatus::Unresolved;
  Result.Reason = VerifyReason::QuerySizeLimit;
  Result.Message = "canonical obligation module exceeds query node budget " +
                   std::to_string(MaxQueryNodes);
  Result.BackendName = BackendName.str();
  return Result;
}

static std::optional<std::string>
readSolverOutput(llvm::StringRef Path, std::string &Error, uint64_t Limit) {
  uint64_t Size = 0;
  if (std::error_code EC = llvm::sys::fs::file_size(Path, Size)) {
    Error = "cannot inspect solver output: " + EC.message();
    return std::nullopt;
  }
  if (Size > Limit) {
    Error = "solver output exceeds the " + outputLimitText(Limit) + " limit";
    return std::nullopt;
  }
  auto Buffer = llvm::MemoryBuffer::getFile(Path, false, false);
  if (!Buffer) {
    Error = "cannot read solver output: " + Buffer.getError().message();
    return std::nullopt;
  }
  return (*Buffer)->getBuffer().str();
}

static std::string diagnosticText(llvm::StringRef Text) {
  Text = Text.trim();
  if (Text.size() > 1024)
    Text = Text.take_front(1024);
  return Text.str();
}

enum class ProcessPollState { Running, Exited, Failed };

struct ProcessPollResult {
  ProcessPollState State = ProcessPollState::Running;
  int ExitCode = -1;
  std::string Error;
};

static ProcessPollResult pollProcess(const llvm::sys::ProcessInfo &Process) {
#if defined(_WIN32)
  std::string Error;
  llvm::sys::ProcessInfo Waited =
      llvm::sys::Wait(Process, 0, &Error, nullptr, true);
  if (Waited.Pid == llvm::sys::ProcessInfo::InvalidPid)
    return {ProcessPollState::Running, -1, {}};
  if (Waited.Pid != Process.Pid)
    return {ProcessPollState::Failed, -1,
            Error.empty() ? "cannot poll cvc5 process" : std::move(Error)};
  return {ProcessPollState::Exited, Waited.ReturnCode, std::move(Error)};
#else
  int Status = 0;
  pid_t Waited;
  do {
    Waited = ::waitpid(Process.Pid, &Status, WNOHANG);
  } while (Waited == -1 && errno == EINTR);
  if (Waited == 0)
    return {};
  if (Waited == -1)
    return {ProcessPollState::Failed, -1,
            "cannot poll cvc5 process: " +
                std::error_code(errno, std::generic_category()).message()};
  if (WIFEXITED(Status))
    return {ProcessPollState::Exited, WEXITSTATUS(Status), {}};
  if (WIFSIGNALED(Status))
    return {ProcessPollState::Exited, -2,
            "cvc5 terminated by signal " + std::to_string(WTERMSIG(Status))};
  return {ProcessPollState::Failed, -1,
          "cvc5 changed to an unsupported process state"};
#endif
}

static bool terminateAndReap(const llvm::sys::ProcessInfo &Process,
                             std::string &Error) {
#if defined(_WIN32)
  if (!::TerminateProcess(static_cast<HANDLE>(Process.Process), 1) &&
      ::GetLastError() != ERROR_ACCESS_DENIED) {
    Error = "cannot terminate cvc5 process";
    return false;
  }
  std::string WaitError;
  llvm::sys::ProcessInfo Waited =
      llvm::sys::Wait(Process, std::nullopt, &WaitError);
  if (Waited.Pid != Process.Pid) {
    Error =
        WaitError.empty() ? "cannot reap cvc5 process" : std::move(WaitError);
    return false;
  }
  return true;
#else
  if (::kill(Process.Pid, SIGKILL) == -1 && errno != ESRCH) {
    Error = "cannot terminate cvc5 process: " +
            std::error_code(errno, std::generic_category()).message();
    return false;
  }
  int Status = 0;
  pid_t Waited;
  do {
    Waited = ::waitpid(Process.Pid, &Status, 0);
  } while (Waited == -1 && errno == EINTR);
  if (Waited == -1 && errno != ECHILD) {
    Error = "cannot reap cvc5 process: " +
            std::error_code(errno, std::generic_category()).message();
    return false;
  }
  return true;
#endif
}

static bool startsWithSat(llvm::StringRef OutputPath) {
  auto Buffer = llvm::MemoryBuffer::getFileSlice(OutputPath, 4, 0, false);
  return Buffer && (*Buffer)->getBuffer() == "sat\n";
}

static bool solverOutputWithinLimit(llvm::StringRef OutputPath,
                                    llvm::StringRef ErrorPath,
                                    std::string &Error, bool &LimitExceeded) {
  uint64_t OutputSize = 0;
  uint64_t ErrorSize = 0;
  if (std::error_code EC = llvm::sys::fs::file_size(OutputPath, OutputSize)) {
    Error = "cannot inspect cvc5 output: " + EC.message();
    return false;
  }
  if (std::error_code EC = llvm::sys::fs::file_size(ErrorPath, ErrorSize)) {
    Error = "cannot inspect cvc5 error output: " + EC.message();
    return false;
  }
  // Only a model may exceed a line; it follows the verdict.
  const uint64_t OutputLimit =
      OutputSize > MaxSolverOutputBytes && !startsWithSat(OutputPath)
          ? MaxSolverOutputBytes
          : MaxModelOutputBytes;
  if (OutputSize > OutputLimit || ErrorSize > MaxSolverOutputBytes) {
    LimitExceeded = true;
    Error =
        "solver output exceeds the " +
        outputLimitText(ErrorSize > MaxSolverOutputBytes ? MaxSolverOutputBytes
                                                         : OutputLimit) +
        " limit";
    return false;
  }
  return true;
}

/// An s-expression of solver output.
struct SExpr {
  bool IsList = false;
  std::string Atom;
  std::vector<SExpr> List;
};

constexpr unsigned MaxModelNesting = 20000;

/// Read one s-expression starting at Pos without recursion.
std::optional<SExpr> readSExpr(llvm::StringRef Text, size_t &Pos) {
  auto skip = [&] {
    while (Pos < Text.size()) {
      const char C = Text[Pos];
      if (C == ';') {
        while (Pos < Text.size() && Text[Pos] != '\n')
          ++Pos;
      } else if (C == ' ' || C == '\t' || C == '\n' || C == '\r') {
        ++Pos;
      } else {
        break;
      }
    }
  };
  std::vector<SExpr> Open;
  while (true) {
    skip();
    if (Pos >= Text.size())
      return std::nullopt;
    const char C = Text[Pos];
    SExpr Done;
    if (C == '(') {
      if (Open.size() >= MaxModelNesting)
        return std::nullopt;
      ++Pos;
      Open.emplace_back();
      Open.back().IsList = true;
      continue;
    }
    if (C == ')') {
      if (Open.empty())
        return std::nullopt;
      ++Pos;
      Done = std::move(Open.back());
      Open.pop_back();
    } else if (C == '|') {
      const size_t End = Text.find('|', Pos + 1);
      if (End == llvm::StringRef::npos)
        return std::nullopt;
      Done.Atom = Text.substr(Pos + 1, End - Pos - 1).str();
      Pos = End + 1;
    } else {
      const size_t Start = Pos;
      while (Pos < Text.size() && Text[Pos] != '(' && Text[Pos] != ')' &&
             Text[Pos] != ' ' && Text[Pos] != '\t' && Text[Pos] != '\n' &&
             Text[Pos] != '\r')
        ++Pos;
      Done.Atom = Text.substr(Start, Pos - Start).str();
    }
    if (Open.empty())
      return Done;
    Open.back().List.push_back(std::move(Done));
  }
}

/// A value of an SMT-LIB sort in a solver model.
struct SMTValue {
  /// Option is a map cell: none, or some(Integer) when Truth is set.
  enum class Kind { Bool, Int, BitVector, Array, Seq, Option };
  Kind K = Kind::Bool;
  bool Truth = false;
  CertInt Integer;
  llvm::APInt Bits;
  /// An array's cells, as integers: Bool ones as 0 or 1, option ones as
  /// whether they are some, with their values in Values.
  HeapValue Heap;
  HeapValue Values;
  Kind Cells = Kind::Int;
  std::vector<CertInt> Elements;

  std::string key() const {
    switch (K) {
    case Kind::Bool:
      return Truth ? "true" : "false";
    case Kind::Int:
      return Integer.toDecimal();
    case Kind::BitVector:
      return "#" + std::to_string(Bits.getBitWidth()) + ":" +
             decimalUnsigned(Bits);
    case Kind::Array:
      return std::to_string(static_cast<int>(Cells)) +
             LogicValue::heap(Heap).key() +
             (Cells == Kind::Option ? LogicValue::heap(Values).key() : "");
    case Kind::Seq:
      return LogicValue::sequence(Elements).key();
    case Kind::Option:
      return Truth ? "some " + Integer.toDecimal() : "none";
    }
    return {};
  }

  /// The cell of an array, as a value of its kind.
  SMTValue cell(const CertInt &Index) const;
  /// Sets the cell of an array to \p Value, which must be of its kind.
  bool set(const CertInt &Index, const SMTValue &Value);
  friend bool operator==(const SMTValue &L, const SMTValue &R) {
    return L.K == R.K && L.key() == R.key();
  }
};

SMTValue smtBool(bool Truth) {
  SMTValue Value;
  Value.K = SMTValue::Kind::Bool;
  Value.Truth = Truth;
  return Value;
}

SMTValue smtInt(CertInt Integer) {
  SMTValue Value;
  Value.K = SMTValue::Kind::Int;
  Value.Integer = std::move(Integer);
  return Value;
}

SMTValue smtBits(llvm::APInt Bits) {
  SMTValue Value;
  Value.K = SMTValue::Kind::BitVector;
  Value.Bits = std::move(Bits);
  return Value;
}

SMTValue smtOption(std::optional<CertInt> Some) {
  SMTValue Value;
  Value.K = SMTValue::Kind::Option;
  Value.Truth = Some.has_value();
  if (Some)
    Value.Integer = std::move(*Some);
  return Value;
}

SMTValue SMTValue::cell(const CertInt &Index) const {
  const CertInt Stored = Heap.get(Index);
  if (Cells == Kind::Bool)
    return smtBool(!Stored.isZero());
  if (Cells == Kind::Option)
    return Stored.isZero() ? smtOption(std::nullopt)
                           : smtOption(Values.get(Index));
  return smtInt(Stored);
}

bool SMTValue::set(const CertInt &Index, const SMTValue &Value) {
  if (Value.K != Cells)
    return false;
  if (Cells == Kind::Bool) {
    Heap.set(Index, CertInt(Value.Truth ? 1 : 0));
  } else if (Cells == Kind::Option) {
    Heap.set(Index, CertInt(Value.Truth ? 1 : 0));
    Values.set(Index, Value.Truth ? Value.Integer : CertInt(0));
  } else {
    Heap.set(Index, Value.Integer);
  }
  return true;
}

using SMTEnvironment = std::vector<std::pair<std::string, SMTValue>>;

/// Evaluate a closed model term: literals, the core and arithmetic
/// connectives, arrays, and let. Anything else is unsupported.
std::optional<SMTValue> evaluateModelTerm(const SExpr &E,
                                          SMTEnvironment &Environment,
                                          unsigned Depth = 0) {
  if (Depth > MaxModelNesting)
    return std::nullopt;
  auto eval = [&](const SExpr &Child) {
    return evaluateModelTerm(Child, Environment, Depth + 1);
  };
  if (!E.IsList) {
    llvm::StringRef Atom = E.Atom;
    if (Atom == "true" || Atom == "false")
      return smtBool(Atom == "true");
    if (Atom == "cppverify.none")
      return smtOption(std::nullopt);
    for (auto It = Environment.rbegin(); It != Environment.rend(); ++It)
      if (It->first == Atom)
        return It->second;
    if (Atom.consume_front("#b") && !Atom.empty())
      return smtBits(llvm::APInt(Atom.size(), Atom, 2));
    if (Atom.consume_front("#x") && !Atom.empty())
      return smtBits(llvm::APInt(Atom.size() * 4, Atom, 16));
    if (std::optional<CertInt> Integer = CertInt::fromDecimal(E.Atom);
        Integer && !llvm::StringRef(E.Atom).starts_with("-"))
      return smtInt(*Integer);
    return std::nullopt;
  }
  if (E.List.empty())
    return std::nullopt;
  const SExpr &Head = E.List.front();
  // ((as const (Array Int Int)) v)
  if (Head.IsList) {
    if (E.List.size() != 2 || Head.List.size() != 3 || Head.List[0].IsList ||
        Head.List[0].Atom != "as" || Head.List[1].IsList ||
        Head.List[1].Atom != "const")
      return std::nullopt;
    std::optional<SMTValue> Default = eval(E.List[1]);
    if (!Default || (Default->K != SMTValue::Kind::Int &&
                     Default->K != SMTValue::Kind::Bool &&
                     Default->K != SMTValue::Kind::Option))
      return std::nullopt;
    SMTValue Array;
    Array.K = SMTValue::Kind::Array;
    Array.Cells = Default->K;
    if (Default->K == SMTValue::Kind::Int) {
      Array.Heap.Default = Default->Integer;
    } else {
      Array.Heap.Default = CertInt(Default->Truth ? 1 : 0);
      if (Default->K == SMTValue::Kind::Option && Default->Truth)
        Array.Values.Default = Default->Integer;
    }
    return Array;
  }
  const std::string &Op = Head.Atom;
  const size_t Arity = E.List.size() - 1;
  // (as seq.empty (Seq Int))
  if (Op == "as" && Arity == 2 && !E.List[1].IsList &&
      E.List[1].Atom == "seq.empty") {
    SMTValue Empty;
    Empty.K = SMTValue::Kind::Seq;
    return Empty;
  }
  if (Op == "_") {
    if (Arity != 2 || E.List[1].IsList || E.List[2].IsList)
      return std::nullopt;
    llvm::StringRef Name = E.List[1].Atom;
    unsigned Width = 0;
    if (!Name.consume_front("bv") ||
        llvm::StringRef(E.List[2].Atom).getAsInteger(10, Width) || Width == 0 ||
        Width > MaxLogicIntegerBitWidth)
      return std::nullopt;
    std::optional<CertInt> Value = CertInt::fromDecimal(Name);
    if (!Value || Value->isNegative())
      return std::nullopt;
    return smtBits(Value->bits(Width));
  }
  if (Op == "let") {
    if (Arity != 2 || !E.List[1].IsList)
      return std::nullopt;
    SMTEnvironment Bound;
    for (const SExpr &Binding : E.List[1].List) {
      if (!Binding.IsList || Binding.List.size() != 2 || Binding.List[0].IsList)
        return std::nullopt;
      std::optional<SMTValue> Value = eval(Binding.List[1]);
      if (!Value)
        return std::nullopt;
      Bound.emplace_back(Binding.List[0].Atom, std::move(*Value));
    }
    const size_t Saved = Environment.size();
    Environment.insert(Environment.end(), Bound.begin(), Bound.end());
    std::optional<SMTValue> Value = eval(E.List[2]);
    Environment.resize(Saved);
    return Value;
  }
  if (Op == "ite") {
    if (Arity != 3)
      return std::nullopt;
    std::optional<SMTValue> Condition = eval(E.List[1]);
    if (!Condition || Condition->K != SMTValue::Kind::Bool)
      return std::nullopt;
    return eval(E.List[Condition->Truth ? 2 : 3]);
  }
  std::vector<SMTValue> Args;
  for (size_t I = 1; I != E.List.size(); ++I) {
    std::optional<SMTValue> Value = eval(E.List[I]);
    if (!Value)
      return std::nullopt;
    Args.push_back(std::move(*Value));
  }
  auto allOf = [&](SMTValue::Kind Kind) {
    return llvm::all_of(Args,
                        [Kind](const SMTValue &Arg) { return Arg.K == Kind; });
  };
  if (Op == "seq.unit") {
    if (Arity != 1 || Args[0].K != SMTValue::Kind::Int)
      return std::nullopt;
    SMTValue Unit;
    Unit.K = SMTValue::Kind::Seq;
    Unit.Elements.push_back(Args[0].Integer);
    return Unit;
  }
  // cvc5 prints sequence concatenation as str.++.
  if (Op == "seq.++" || Op == "str.++") {
    if (Args.empty() || !allOf(SMTValue::Kind::Seq))
      return std::nullopt;
    SMTValue Joined;
    Joined.K = SMTValue::Kind::Seq;
    for (const SMTValue &Part : Args)
      Joined.Elements.insert(Joined.Elements.end(), Part.Elements.begin(),
                             Part.Elements.end());
    return Joined;
  }
  if (Op == "=" || Op == "distinct") {
    if (Arity < 2)
      return std::nullopt;
    for (size_t I = 1; I != Args.size(); ++I)
      if (Args[I].K != Args[0].K)
        return std::nullopt;
    if (Op == "=")
      return smtBool(llvm::all_of(
          Args, [&](const SMTValue &Arg) { return Arg == Args[0]; }));
    std::set<std::string> Keys;
    for (const SMTValue &Arg : Args)
      if (!Keys.insert(Arg.key()).second)
        return smtBool(false);
    return smtBool(true);
  }
  if (Op == "not" || Op == "and" || Op == "or" || Op == "=>" || Op == "xor") {
    if (!allOf(SMTValue::Kind::Bool) || Args.empty())
      return std::nullopt;
    if (Op == "not")
      return Arity == 1 ? std::optional<SMTValue>(smtBool(!Args[0].Truth))
                        : std::nullopt;
    if (Op == "and")
      return smtBool(
          llvm::all_of(Args, [](const SMTValue &A) { return A.Truth; }));
    if (Op == "or")
      return smtBool(
          llvm::any_of(Args, [](const SMTValue &A) { return A.Truth; }));
    if (Arity != 2)
      return std::nullopt;
    if (Op == "=>")
      return smtBool(!Args[0].Truth || Args[1].Truth);
    return smtBool(Args[0].Truth != Args[1].Truth);
  }
  if (Op == "cppverify.some") {
    if (Arity != 1 || Args[0].K != SMTValue::Kind::Int)
      return std::nullopt;
    return smtOption(Args[0].Integer);
  }
  if (Op == "store" || Op == "select") {
    if ((Op == "store") != (Arity == 3) || Args[0].K != SMTValue::Kind::Array ||
        Args[1].K != SMTValue::Kind::Int)
      return std::nullopt;
    if (Op == "select")
      return Arity == 2 ? std::optional<SMTValue>(Args[0].cell(Args[1].Integer))
                        : std::nullopt;
    SMTValue Array = std::move(Args[0]);
    if (!Array.set(Args[1].Integer, Args[2]))
      return std::nullopt;
    return Array;
  }
  if (!allOf(SMTValue::Kind::Int))
    return std::nullopt;
  if (Op == "-") {
    if (Arity == 1)
      return smtInt(-Args[0].Integer);
    CertInt Value = Args[0].Integer;
    for (size_t I = 1; I != Args.size(); ++I)
      Value = Value - Args[I].Integer;
    return smtInt(std::move(Value));
  }
  if (Op == "+" || Op == "*") {
    CertInt Value = Args[0].Integer;
    for (size_t I = 1; I != Args.size(); ++I)
      Value = Op == "+" ? Value + Args[I].Integer : Value * Args[I].Integer;
    return smtInt(std::move(Value));
  }
  if (Arity == 2) {
    const CertInt &L = Args[0].Integer;
    const CertInt &R = Args[1].Integer;
    if (Op == "<")
      return smtBool(L < R);
    if (Op == "<=")
      return smtBool(!(R < L));
    if (Op == ">")
      return smtBool(R < L);
    if (Op == ">=")
      return smtBool(!(L < R));
  }
  return std::nullopt;
}

/// One define-fun of a model. An ite chain on parameter equalities is indexed
/// by argument values; what remains is evaluated per application.
struct ModelDefinition {
  std::vector<std::string> Parameters;
  SExpr Body;
  bool Indexed = false;
  std::map<std::string, SMTValue> Entries;
  const SExpr *Rest = nullptr;

  static std::string keyOf(const std::vector<SMTValue> &Arguments) {
    std::string Key;
    for (const SMTValue &Argument : Arguments)
      Key += "\x1f" + Argument.key();
    return Key;
  }

  /// The parameter values an equality conjunction fixes, one per parameter.
  bool matchCondition(const SExpr &Condition,
                      std::vector<std::optional<SMTValue>> &Fixed) const {
    if (!Condition.IsList || Condition.List.empty() || Condition.List[0].IsList)
      return false;
    if (Condition.List[0].Atom == "and") {
      for (size_t I = 1; I != Condition.List.size(); ++I)
        if (!matchCondition(Condition.List[I], Fixed))
          return false;
      return true;
    }
    if (Condition.List[0].Atom != "=" || Condition.List.size() != 3)
      return false;
    for (unsigned Side = 1; Side <= 2; ++Side) {
      const SExpr &Name = Condition.List[Side];
      if (Name.IsList)
        continue;
      auto It = llvm::find(Parameters, Name.Atom);
      if (It == Parameters.end())
        continue;
      SMTEnvironment Closed;
      std::optional<SMTValue> Value =
          evaluateModelTerm(Condition.List[3 - Side], Closed);
      const size_t Index = It - Parameters.begin();
      if (!Value || Fixed[Index])
        return false;
      Fixed[Index] = std::move(*Value);
      return true;
    }
    return false;
  }

  void index() {
    Indexed = true;
    const SExpr *Current = &Body;
    while (Current->IsList && Current->List.size() == 4 &&
           !Current->List[0].IsList && Current->List[0].Atom == "ite") {
      std::vector<std::optional<SMTValue>> Fixed(Parameters.size());
      if (!matchCondition(Current->List[1], Fixed) ||
          llvm::any_of(Fixed, [](const std::optional<SMTValue> &Value) {
            return !Value;
          }))
        break;
      SMTEnvironment Closed;
      std::optional<SMTValue> Value =
          evaluateModelTerm(Current->List[2], Closed);
      if (!Value)
        break;
      std::vector<SMTValue> Arguments;
      for (auto &Argument : Fixed)
        Arguments.push_back(std::move(*Argument));
      Entries.emplace(keyOf(Arguments), std::move(*Value));
      Current = &Current->List[3];
    }
    Rest = Current;
  }

  std::optional<SMTValue> apply(const std::vector<SMTValue> &Arguments) {
    if (Arguments.size() != Parameters.size())
      return std::nullopt;
    if (!Indexed)
      index();
    if (auto It = Entries.find(keyOf(Arguments)); It != Entries.end())
      return It->second;
    SMTEnvironment Environment;
    for (size_t I = 0; I != Parameters.size(); ++I)
      Environment.emplace_back(Parameters[I], Arguments[I]);
    return evaluateModelTerm(*Rest, Environment);
  }
};

/// A printed sequence value: (str.++ (seq.unit c) ...) over integer
/// constants c.
bool isSequenceConstant(const SExpr &E) {
  if (!E.IsList || E.List.size() < 3 || E.List[0].IsList ||
      (E.List[0].Atom != "str.++" && E.List[0].Atom != "seq.++"))
    return false;
  for (size_t I = 1; I != E.List.size(); ++I) {
    const SExpr &Unit = E.List[I];
    if (!Unit.IsList || Unit.List.size() != 2 || Unit.List[0].IsList ||
        Unit.List[0].Atom != "seq.unit")
      return false;
    const SExpr &Element = Unit.List[1];
    const bool Numeral =
        !Element.IsList ||
        (Element.List.size() == 2 && !Element.List[0].IsList &&
         Element.List[0].Atom == "-" && !Element.List[1].IsList);
    if (!Numeral || (!Element.IsList && !CertInt::fromDecimal(Element.Atom)) ||
        (Element.IsList && !CertInt::fromDecimal(Element.List[1].Atom)))
      return false;
  }
  return true;
}

/// The define-fun list cvc5 prints after sat. With \p ReversedSequences,
/// sequence values are printed last element first and are read reversed.
llvm::Expected<std::map<std::string, ModelDefinition>>
parseModel(llvm::StringRef Text, bool ReversedSequences = false) {
  auto malformed = [](llvm::StringRef Why) {
    return llvm::createStringError(llvm::inconvertibleErrorCode(),
                                   "malformed cvc5 model: %s",
                                   Why.str().c_str());
  };
  size_t Pos = 0;
  std::optional<SExpr> Root = readSExpr(Text, Pos);
  if (!Root || !Root->IsList)
    return malformed("no model follows sat");
  if (!Text.drop_front(Pos).trim().empty())
    return malformed("unexpected text after the model");
  if (ReversedSequences) {
    std::vector<SExpr *> Work = {&*Root};
    while (!Work.empty()) {
      SExpr *Current = Work.back();
      Work.pop_back();
      if (isSequenceConstant(*Current)) {
        std::reverse(Current->List.begin() + 1, Current->List.end());
        continue;
      }
      for (SExpr &Child : Current->List)
        if (Child.IsList)
          Work.push_back(&Child);
    }
  }
  std::map<std::string, ModelDefinition> Definitions;
  for (SExpr &Entry : Root->List) {
    if (!Entry.IsList || Entry.List.size() != 5 || Entry.List[0].IsList ||
        Entry.List[0].Atom != "define-fun" || Entry.List[1].IsList ||
        !Entry.List[2].IsList)
      return malformed("expected define-fun");
    ModelDefinition Definition;
    for (const SExpr &Parameter : Entry.List[2].List) {
      if (!Parameter.IsList || Parameter.List.size() != 2 ||
          Parameter.List[0].IsList)
        return malformed("bad parameter");
      Definition.Parameters.push_back(Parameter.List[0].Atom);
    }
    Definition.Body = std::move(Entry.List[4]);
    if (!Definitions.emplace(Entry.List[1].Atom, std::move(Definition)).second)
      return malformed("duplicate definition");
  }
  return Definitions;
}

/// A cvc5 model read through the encoding that produced its query.
class CVC5CandidateModel : public CandidateModel {
  std::map<std::string, ModelDefinition> &Definitions;
  const bool IntegerMode;
  const std::set<std::string> &Defined;

  std::optional<SMTValue> toSMT(const LogicValue &Value,
                                const LogicSort &Sort) const {
    switch (Value.K) {
    case LogicValue::Kind::Bool:
      return smtBool(Value.Truth);
    case LogicValue::Kind::Heap: {
      SMTValue Array;
      Array.K = SMTValue::Kind::Array;
      Array.Heap = *Value.Heap;
      return Array;
    }
    case LogicValue::Kind::Integer:
      if (Sort.Kind == LogicSortKind::BitVector && !IntegerMode)
        return smtBits(Value.Integer.bits(Sort.BitWidth));
      return smtInt(Value.Integer);
    case LogicValue::Kind::Seq: {
      SMTValue Sequence;
      Sequence.K = SMTValue::Kind::Seq;
      Sequence.Elements = *Value.Elements;
      return Sequence;
    }
    case LogicValue::Kind::Set:
    case LogicValue::Kind::Multiset: {
      SMTValue Array;
      Array.K = SMTValue::Kind::Array;
      Array.Cells = Value.K == LogicValue::Kind::Set ? SMTValue::Kind::Bool
                                                     : SMTValue::Kind::Int;
      Array.Heap = *Value.Heap;
      return Array;
    }
    case LogicValue::Kind::Map: {
      SMTValue Array;
      Array.K = SMTValue::Kind::Array;
      Array.Cells = SMTValue::Kind::Option;
      Array.Heap = *Value.Heap;
      Array.Values = *Value.Values;
      return Array;
    }
    }
    return std::nullopt;
  }

  /// \p Opaque applications of machine-sorted functions are read reduced in
  /// range in the integer encoding, as the query reads them.
  std::optional<LogicValue> fromSMT(const std::optional<SMTValue> &Value,
                                    const LogicSort &Sort, bool Opaque) const {
    if (!Value)
      return std::nullopt;
    switch (Sort.Kind) {
    case LogicSortKind::Bool:
      if (Value->K == SMTValue::Kind::Bool)
        return LogicValue::boolean(Value->Truth);
      return std::nullopt;
    case LogicSortKind::Heap:
      if (Value->K == SMTValue::Kind::Array &&
          Value->Cells == SMTValue::Kind::Int)
        return LogicValue::heap(Value->Heap);
      return std::nullopt;
    case LogicSortKind::Seq:
      if (Value->K == SMTValue::Kind::Seq)
        return LogicValue::sequence(Value->Elements);
      return std::nullopt;
    case LogicSortKind::Set:
      if (Value->K == SMTValue::Kind::Array &&
          Value->Cells == SMTValue::Kind::Bool)
        return LogicValue::set(Value->Heap);
      return std::nullopt;
    case LogicSortKind::Multiset:
      if (Value->K == SMTValue::Kind::Array &&
          Value->Cells == SMTValue::Kind::Int)
        return LogicValue::multiset(Value->Heap);
      return std::nullopt;
    case LogicSortKind::Map:
      if (Value->K == SMTValue::Kind::Array &&
          Value->Cells == SMTValue::Kind::Option)
        return LogicValue::map(Value->Heap, Value->Values);
      return std::nullopt;
    case LogicSortKind::MathematicalInteger:
    case LogicSortKind::Pointer:
      if (Value->K == SMTValue::Kind::Int)
        return LogicValue::integer(Value->Integer);
      return std::nullopt;
    case LogicSortKind::BitVector:
      if (Value->K == SMTValue::Kind::BitVector &&
          Value->Bits.getBitWidth() == Sort.BitWidth)
        return LogicValue::integer(CertInt::fromBits(
            Value->Bits, Sort.Signedness == LogicSignedness::Signed));
      if (Value->K == SMTValue::Kind::Int && IntegerMode)
        return LogicValue::integer(
            Opaque
                ? CertInt::fromBits(Value->Integer.bits(Sort.BitWidth),
                                    Sort.Signedness == LogicSignedness::Signed)
                : Value->Integer);
      return std::nullopt;
    case LogicSortKind::Invalid:
      break;
    }
    return std::nullopt;
  }

  ModelDefinition *find(const std::string &Name) {
    auto It = Definitions.find(Name);
    return It == Definitions.end() ? nullptr : &It->second;
  }

public:
  CVC5CandidateModel(std::map<std::string, ModelDefinition> &Definitions,
                     bool IntegerMode, const std::set<std::string> &Defined)
      : Definitions(Definitions), IntegerMode(IntegerMode), Defined(Defined) {}

  bool defined(const LogicFunctionDecl &Function) override {
    return Defined.count(Function.Identity);
  }

  std::optional<LogicValue> constant(const std::string &Name,
                                     const LogicSort &Sort) override {
    ModelDefinition *Definition = find(smtSymbol("v_", Name));
    if (!Definition || !Definition->Parameters.empty())
      return std::nullopt;
    return fromSMT(Definition->apply({}), Sort, /*Opaque=*/false);
  }

  std::optional<bool> validPointer(const CertInt &Address) override {
    ModelDefinition *Definition = find("p_valid");
    if (!Definition)
      return std::nullopt;
    std::optional<SMTValue> Valid = Definition->apply({smtInt(Address)});
    if (!Valid || Valid->K != SMTValue::Kind::Bool)
      return std::nullopt;
    return Valid->Truth;
  }

  std::optional<LogicValue>
  application(const LogicFunctionDecl &Function,
              const std::vector<LogicValue> &Arguments) override {
    ModelDefinition *Definition = find(smtSymbol("f_", Function.Identity));
    if (!Definition || defined(Function) ||
        Arguments.size() != Function.Parameters.size())
      return std::nullopt;
    std::vector<SMTValue> Values;
    for (unsigned I = 0; I != Arguments.size(); ++I) {
      std::optional<SMTValue> Value =
          toSMT(Arguments[I], Function.Parameters[I].Sort);
      if (!Value)
        return std::nullopt;
      Values.push_back(std::move(*Value));
    }
    return fromSMT(Definition->apply(Values), Function.ResultSort,
                   /*Opaque=*/true);
  }
};

} // namespace

llvm::Expected<std::string>
verify::encodeSMTLibQuery(const ObligationModule &Module,
                          const LogicExpr *Query,
                          MachineIntegerEncoding Encoding) {
  auto Features = validateObligationModule(Module);
  if (!Features)
    return Features.takeError();
  if (*Features != Module.RequiredFeatures)
    return llvm::createStringError(
        llvm::inconvertibleErrorCode(),
        "obligation feature declaration does not match validated contents");
  if (Encoding != MachineIntegerEncoding::Auto)
    return SMTLibEncoder(Module, Encoding).run(Query);
  SMTLibEncoder Integer(Module, MachineIntegerEncoding::Integer);
  llvm::Expected<std::string> Script = Integer.run(Query);
  if (!Script || !Integer.usedBitLevelOperation())
    return Script;
  return SMTLibEncoder(Module, MachineIntegerEncoding::BitVector).run(Query);
}

VerifyResult
verify::lowerSMTLibModule(const ObligationModule &Module,
                          llvm::raw_ostream *SMTLibOut,
                          const BackendExecutionOptions &Execution) {
  VerifyResult Limited =
      querySizeLimitResult(Module, Execution.MaxQueryNodes, "cvc5");
  if (Limited.Reason != VerifyReason::None)
    return Limited;
  auto Script = encodeSMTLibQuery(Module, Module.CounterexampleQuery.get(),
                                  Execution.IntegerEncoding);
  if (!Script) {
    VerifyResult Result;
    Result.Status = VerifyStatus::Unresolved;
    Result.Reason = VerifyReason::EncodingFailure;
    Result.BackendName = "cvc5";
    Result.Message = llvm::toString(Script.takeError());
    return Result;
  }
  if (SMTLibOut)
    *SMTLibOut << *Script;
  VerifyResult Result;
  Result.Status = VerifyStatus::Lowered;
  Result.BackendName = "cvc5";
  return Result;
}

CVC5VerifyBackend::CVC5VerifyBackend(const BackendExecutionOptions &Execution)
    : TimeoutMs(Execution.SolverTimeoutMs),
      CollectionTimeoutMs(Execution.CollectionTimeoutMs),
      CertifyTimeoutMs(Execution.CertifyTimeoutMs),
      ResourceLimit(Execution.SolverResourceLimit), Jobs(Execution.Jobs),
      Pool(Execution.Pool), MaxQueryNodes(Execution.MaxQueryNodes),
      IntegerEncoding(Execution.IntegerEncoding) {
  llvm::StringRef Requested = Execution.CVC5Path.empty()
                                  ? llvm::StringRef("cvc5")
                                  : llvm::StringRef(Execution.CVC5Path);
  auto Program = llvm::sys::findProgramByName(Requested);
  if (Program && llvm::sys::fs::can_execute(*Program))
    SolverPath = *Program;
  else if (!Program)
    SolverPathError = "cannot find cvc5 executable '" + Requested.str() +
                      "': " + Program.getError().message();
  else
    SolverPathError =
        "cvc5 executable is missing or not executable: " + *Program;
}

namespace {
/// A finished cvc5 process's standard output, or why there is none.
struct SolverRun {
  std::optional<std::string> Output;
  VerifyResult Failure;
};
} // namespace

static SolverRun runCVC5(const std::string &SolverPath, llvm::StringRef Script,
                         unsigned TimeoutMs, unsigned ResourceLimit,
                         const std::atomic<bool> *Cancelled = nullptr);

/// Whether the cvc5 at \p SolverPath prints a sequence value last element
/// first, as cvc5 1.1 does (the value itself is right: seq.nth reads it in
/// order). Asked once per executable, with a sequence of known order.
static bool printsSequencesReversed(const std::string &SolverPath) {
  static std::mutex Lock;
  static std::map<std::string, bool> Known;
  std::lock_guard<std::mutex> Guard(Lock);
  if (auto It = Known.find(SolverPath); It != Known.end())
    return It->second;
  bool Reversed = false;
  SolverRun Run = runCVC5(SolverPath,
                          "(set-logic ALL)\n"
                          "(declare-fun x () (Seq Int))\n"
                          "(assert (= x (seq.++ (seq.unit 1) (seq.unit 2))))\n"
                          "(check-sat)\n",
                          10000, 0);
  if (Run.Output) {
    const auto [Verdict, Rest] = llvm::StringRef(*Run.Output).split('\n');
    if (Verdict.trim() == "sat") {
      if (auto Definitions = parseModel(Rest)) {
        if (auto It = Definitions->find("x"); It != Definitions->end()) {
          SMTEnvironment Closed;
          std::optional<SMTValue> Value =
              evaluateModelTerm(It->second.Body, Closed);
          Reversed =
              Value && Value->K == SMTValue::Kind::Seq &&
              Value->Elements == std::vector<CertInt>{CertInt(int64_t(2)),
                                                      CertInt(int64_t(1))};
        }
      } else {
        llvm::consumeError(Definitions.takeError());
      }
    }
  }
  Known.emplace(SolverPath, Reversed);
  return Reversed;
}

static SolverRun runCVC5(const std::string &SolverPath, llvm::StringRef Script,
                         unsigned TimeoutMs, unsigned ResourceLimit,
                         const std::atomic<bool> *Cancelled) {
  SolverRun Run;
  VerifyResult &Result = Run.Failure;
  Result.BackendName = "cvc5";
  Result.Status = VerifyStatus::Unresolved;
  int InputFD = -1;
  llvm::SmallString<128> InputPath;
  if (std::error_code EC = llvm::sys::fs::createTemporaryFile(
          "cppverify-cvc5", "smt2", InputFD, InputPath)) {
    Result.Reason = VerifyReason::SolverInvocationFailure;
    Result.Message = "cannot create cvc5 input: " + EC.message();
    return Run;
  }
  llvm::FileRemover RemoveInput(InputPath);
  {
    llvm::raw_fd_ostream Input(InputFD, true);
    Input << Script;
    Input.flush();
    if (Input.has_error()) {
      Result.Reason = VerifyReason::SolverInvocationFailure;
      Result.Message = "cannot write cvc5 input: " + Input.error().message();
      Input.clear_error();
      return Run;
    }
  }

  llvm::SmallString<128> OutputPath;
  if (std::error_code EC = llvm::sys::fs::createTemporaryFile(
          "cppverify-cvc5", "out", OutputPath)) {
    Result.Reason = VerifyReason::SolverInvocationFailure;
    Result.Message = "cannot create cvc5 output: " + EC.message();
    return Run;
  }
  llvm::FileRemover RemoveOutput(OutputPath);
  llvm::SmallString<128> ErrorPath;
  if (std::error_code EC = llvm::sys::fs::createTemporaryFile(
          "cppverify-cvc5", "err", ErrorPath)) {
    Result.Reason = VerifyReason::SolverInvocationFailure;
    Result.Message = "cannot create cvc5 error output: " + EC.message();
    return Run;
  }
  llvm::FileRemover RemoveError(ErrorPath);

  std::vector<std::string> OwnedArgs = {SolverPath, "--lang=smt2", "--seed=0",
                                        "--sat-random-seed=0", "--dump-models"};
  if (TimeoutMs != 0)
    OwnedArgs.push_back("--tlimit-per=" + std::to_string(TimeoutMs));
  if (ResourceLimit != 0)
    OwnedArgs.push_back("--rlimit-per=" + std::to_string(ResourceLimit));
  OwnedArgs.push_back(InputPath.str().str());
  llvm::SmallVector<llvm::StringRef, 8> Args;
  for (const std::string &Argument : OwnedArgs)
    Args.push_back(Argument);
  std::optional<llvm::StringRef> Redirects[] = {std::nullopt, OutputPath.str(),
                                                ErrorPath.str()};
  std::string InvocationError;
  bool ExecutionFailed = false;
  llvm::sys::ProcessInfo Process =
      llvm::sys::ExecuteNoWait(SolverPath, Args, std::nullopt, Redirects, 0,
                               &InvocationError, &ExecutionFailed);
  if (ExecutionFailed || Process.Pid == llvm::sys::ProcessInfo::InvalidPid) {
    Result.Reason = VerifyReason::SolverInvocationFailure;
    Result.Message = InvocationError.empty() ? "cannot start cvc5 process"
                                             : std::move(InvocationError);
    return Run;
  }

  const auto Deadline = std::chrono::steady_clock::now() +
                        std::chrono::milliseconds(TimeoutMs) +
                        std::chrono::seconds(1);
  int ExitCode = -1;
  bool TimedOut = false;
  bool Stopped = false;
  bool OutputLimitExceeded = false;
  while (true) {
    ProcessPollResult Poll = pollProcess(Process);
    if (Poll.State == ProcessPollState::Exited) {
      ExitCode = Poll.ExitCode;
      InvocationError = std::move(Poll.Error);
      break;
    }
    if (Poll.State == ProcessPollState::Failed) {
      InvocationError = std::move(Poll.Error);
      std::string TerminationError;
      if (!terminateAndReap(Process, TerminationError) &&
          !TerminationError.empty())
        InvocationError += ": " + TerminationError;
      break;
    }

    std::string OutputError;
    if (!solverOutputWithinLimit(OutputPath, ErrorPath, OutputError,
                                 OutputLimitExceeded)) {
      InvocationError = std::move(OutputError);
      std::string TerminationError;
      if (!terminateAndReap(Process, TerminationError) &&
          !TerminationError.empty())
        InvocationError += ": " + TerminationError;
      break;
    }
    if (Cancelled && *Cancelled) {
      Stopped = true;
      std::string TerminationError;
      if (!terminateAndReap(Process, TerminationError))
        InvocationError = std::move(TerminationError);
      break;
    }
    if (TimeoutMs != 0 && std::chrono::steady_clock::now() >= Deadline) {
      TimedOut = true;
      std::string TerminationError;
      if (!terminateAndReap(Process, TerminationError))
        InvocationError = std::move(TerminationError);
      break;
    }
    std::this_thread::sleep_for(std::chrono::milliseconds(2));
  }

  std::string ReadError;
  std::optional<std::string> StandardError =
      readSolverOutput(ErrorPath, ReadError, MaxSolverOutputBytes);
  if (!StandardError) {
    Result.Reason = VerifyReason::SolverMalformedOutput;
    Result.Message = std::move(ReadError);
    return Run;
  }
  if (OutputLimitExceeded) {
    Result.Reason = VerifyReason::SolverMalformedOutput;
    Result.Message = std::move(InvocationError);
    return Run;
  }
  if (TimedOut) {
    Result.Reason = VerifyReason::SolverTimeout;
    Result.Message = InvocationError.empty() ? "cvc5 process timed out"
                                             : std::move(InvocationError);
    return Run;
  }
  if (Stopped) {
    Result.Reason = VerifyReason::SolverUnknown;
    Result.Message = "stopped: another solver settled the query";
    return Run;
  }
  if (ExitCode != 0) {
    Result.Reason = VerifyReason::SolverInvocationFailure;
    Result.Message = "cvc5 exited with status " + std::to_string(ExitCode);
    if (!InvocationError.empty())
      Result.Message += ": " + InvocationError;
    if (!StandardError->empty())
      Result.Message += ": " + diagnosticText(*StandardError);
    return Run;
  }
  std::optional<std::string> StandardOutput =
      readSolverOutput(OutputPath, ReadError, MaxModelOutputBytes);
  if (StandardOutput && StandardOutput->size() > MaxSolverOutputBytes &&
      !llvm::StringRef(*StandardOutput).starts_with("sat\n")) {
    StandardOutput.reset();
    ReadError = "solver output exceeds the " +
                outputLimitText(MaxSolverOutputBytes) + " limit";
  }
  if (!StandardOutput) {
    Result.Reason = VerifyReason::SolverMalformedOutput;
    Result.Message = std::move(ReadError);
    return Run;
  }
  if (!StandardError->empty()) {
    Result.Reason = VerifyReason::SolverMalformedOutput;
    Result.Message =
        "cvc5 wrote unexpected diagnostics: " + diagnosticText(*StandardError);
    return Run;
  }
  Run.Output = std::move(*StandardOutput);
  return Run;
}

/// Encode a script; Auto resolves once, into \p Encoding.
static llvm::Expected<std::string>
encodeScript(const ObligationModule &Module, const LogicExpr *Query,
             MachineIntegerEncoding &Encoding,
             const std::vector<DefinitionInstance> &Instances,
             const std::vector<const LogicExpr *> &Narrowed,
             std::set<std::string> *Defined = nullptr) {
  auto run = [&](MachineIntegerEncoding Selected, bool *UsedBits) {
    SMTLibEncoder Encoder(Module, Selected);
    Encoder.Instances = Instances;
    Encoder.Narrowed = Narrowed;
    Encoder.DefineFunctions = Defined != nullptr;
    llvm::Expected<std::string> Script = Encoder.run(Query);
    if (UsedBits)
      *UsedBits = Encoder.usedBitLevelOperation();
    if (Defined)
      *Defined = std::move(Encoder.Defined);
    return Script;
  };
  if (Encoding != MachineIntegerEncoding::Auto)
    return run(Encoding, nullptr);
  bool UsedBits = false;
  llvm::Expected<std::string> Script =
      run(MachineIntegerEncoding::Integer, &UsedBits);
  if (!Script || !UsedBits) {
    Encoding = MachineIntegerEncoding::Integer;
    return Script;
  }
  Encoding = MachineIntegerEncoding::BitVector;
  return run(Encoding, nullptr);
}

VerifyResult
CVC5VerifyBackend::verifyQuery(const ObligationModule &Module,
                               const LogicExpr *Query,
                               std::optional<unsigned> BudgetMs) const {
  const unsigned TimeoutMs = withinDeadline(
      BudgetMs ? *BudgetMs
               : moduleTimeoutMs(Module, this->TimeoutMs, CollectionTimeoutMs),
      Deadline);
  VerifyResult Result;
  Result.BackendName = "cvc5";
  Result.Status = VerifyStatus::Unresolved;
  if (SolverPath.empty()) {
    Result.Reason = VerifyReason::SolverUnavailable;
    Result.Message = SolverPathError;
    return Result;
  }
  if (Deadline && std::chrono::steady_clock::now() >= *Deadline) {
    Result.Reason = VerifyReason::SolverTimeout;
    Result.Message = "the function's time (--function-timeout) is spent";
    return Result;
  }
  if (Cancelled) {
    Result.Reason = VerifyReason::SolverUnknown;
    Result.Message = "stopped: another solver settled the query";
    return Result;
  }
  auto Features = validateObligationModule(Module);
  if (!Features || *Features != Module.RequiredFeatures) {
    Result.Reason = VerifyReason::EncodingFailure;
    Result.Message =
        Features ? "obligation feature declaration does not match validated "
                   "contents"
                 : llvm::toString(Features.takeError());
    return Result;
  }
  if (!Query) {
    Result.Reason = VerifyReason::EncodingFailure;
    Result.Message = "missing SMT-LIB counterexample query";
    return Result;
  }

  MachineIntegerEncoding Encoding = IntegerEncoding;
  DefinitionRefinement Refinement(Module, HiddenSearchRounds);
  std::vector<DefinitionInstance> Instances;
  // Once a quantifier range is narrowed, cvc5 only searches among small
  // counterexamples: failing to find one settles nothing.
  std::vector<const LogicExpr *> Narrowed;
  RefinementDecision Unchecked;
  std::vector<VerifyModelValue> UncheckedValues;
  std::string UncheckedApplication;
  std::string UncheckedReason;
  auto unchecked = [&] {
    Result.Reason = Unchecked.Reason;
    Result.Message = Unchecked.Message;
    Result.Unchecked = UncheckedValues;
    Result.UncheckedApplication = UncheckedApplication;
    Result.UncheckedReason = UncheckedReason;
    return Result;
  };
  const auto Start = std::chrono::steady_clock::now();
  std::optional<std::chrono::steady_clock::time_point> QueryDeadline;
  if (TimeoutMs != 0)
    QueryDeadline = Start + std::chrono::milliseconds(TimeoutMs);
  // One check may not spend the whole query.
  auto checkLimits = [&] {
    CertifyLimits Limits;
    Limits.Deadline = QueryDeadline;
    const unsigned CapMs = CertifyTimeoutMs ? *CertifyTimeoutMs : TimeoutMs / 2;
    if (CapMs > 0) {
      const auto Cap =
          std::chrono::steady_clock::now() + std::chrono::milliseconds(CapMs);
      if (!Limits.Deadline || Cap < *Limits.Deadline) {
        Limits.Deadline = Cap;
        Limits.CheckTimeoutMs = CapMs;
      }
    }
    return Limits;
  };
  // Applications at closed arguments are computed, not searched for.
  Instances = closedApplicationInstances(Module, *Query, checkLimits());
  // cvc5 has only instances to refine with; they get a share of the budget.
  const auto Deadline =
      Start + std::chrono::milliseconds(
                  TimeoutMs != 0 ? std::max(TimeoutMs / 5, RefinementShareMs)
                                 : 4 * RefinementShareMs);
  while (true) {
    // Once a hidden instance is given, only a counterexample can come out,
    // and the definitions find one sooner than their values point by point.
    std::set<std::string> Defined;
    auto Script = encodeScript(Module, Query, Encoding, Instances, Narrowed,
                               Refinement.searching() ? &Defined : nullptr);
    if (!Script) {
      Result.Reason = VerifyReason::EncodingFailure;
      Result.Message = llvm::toString(Script.takeError());
      return Result;
    }
    unsigned Budget = TimeoutMs;
    if (Refinement.refined() || !Narrowed.empty()) {
      const auto Remaining =
          std::chrono::duration_cast<std::chrono::milliseconds>(
              Deadline - std::chrono::steady_clock::now())
              .count();
      if (Remaining <= 0) {
        if (!Narrowed.empty())
          return unchecked();
        RefinementDecision Exhausted = Refinement.exhausted();
        Result.Reason = Exhausted.Reason;
        Result.Message = Exhausted.Message;
        return Result;
      }
      Budget = static_cast<unsigned>(Remaining);
    }
    SolverRun Run =
        runCVC5(SolverPath, *Script, Budget, ResourceLimit, &Cancelled);
    auto giveUp = [&](llvm::StringRef Outcome) {
      RefinementDecision Exhausted = Refinement.exhausted(Outcome);
      Result.Reason = Exhausted.Reason;
      Result.Message = Exhausted.Message;
      return Result;
    };
    if (!Run.Output) {
      if (!Narrowed.empty())
        return unchecked();
      if (Refinement.refined() &&
          Run.Failure.Reason == VerifyReason::SolverTimeout)
        return giveUp("then cvc5 timed out");
      return std::move(Run.Failure);
    }
    llvm::StringRef Output = *Run.Output;
    const auto [FirstLine, Rest] = Output.split('\n');
    const llvm::StringRef Verdict = FirstLine.trim();
    // A model cvc5 prints with unknown is a candidate like any other: a
    // counterexample once certified against the definitions.
    if (Verdict == "unknown" && !Rest.trim().empty()) {
      if (auto Candidates =
              parseModel(Rest, printsSequencesReversed(SolverPath))) {
        CVC5CandidateModel Candidate(
            *Candidates, Encoding == MachineIntegerEncoding::Integer, Defined);
        CertifyResult Certified =
            certifyCounterexample(Module, *Query, Candidate, checkLimits());
        if (Certified.Outcome == CertifyOutcome::Certified) {
          Result.Status = VerifyStatus::Failed;
          Result.Reason = VerifyReason::Counterexample;
          Result.CertifiedWith = std::move(Certified.Evidence);
          return Result;
        }
      } else {
        llvm::consumeError(Candidates.takeError());
      }
    }
    if (!Narrowed.empty() && (Verdict == "unsat" || Verdict == "unknown"))
      return unchecked();
    if (Verdict == "unsat" && Rest.trim().empty()) {
      if (std::optional<RefinementDecision> Hidden =
              Refinement.unsatisfiable()) {
        Result.Reason = Hidden->Reason;
        Result.Message = Hidden->Message;
        return Result;
      }
      Result.Status = VerifyStatus::Verified;
      return Result;
    }
    if (Verdict == "unknown" && Refinement.refined())
      return giveUp("then cvc5 returned unknown");
    if (Verdict == "unknown") {
      Result.Reason = VerifyReason::SolverUnknown;
      Result.Message = "cvc5 returned unknown";
      return Result;
    }
    if (Verdict != "sat") {
      Result.Reason = VerifyReason::SolverMalformedOutput;
      Result.Message = Output.trim().empty()
                           ? "cvc5 returned no satisfiability result"
                           : "malformed cvc5 output: " + diagnosticText(Output);
      return Result;
    }
    auto Definitions = parseModel(Rest, printsSequencesReversed(SolverPath));
    if (!Definitions) {
      Result.Reason = VerifyReason::SolverMalformedOutput;
      Result.Message = llvm::toString(Definitions.takeError());
      return Result;
    }
    CVC5CandidateModel Candidate(
        *Definitions, Encoding == MachineIntegerEncoding::Integer, Defined);
    CertifyResult Certified =
        certifyCounterexample(Module, *Query, Candidate, checkLimits());
    if (Certified.Outcome == CertifyOutcome::Undetermined &&
        Narrowed.size() < MaxNarrowedQuantifiers) {
      const LogicExpr *Narrow =
          Certified.DefinitionTooDeep && Certified.DeepApplication
              ? Certified.DeepApplication
              : Certified.WideQuantifier;
      if (Narrow && llvm::find(Narrowed, Narrow) == Narrowed.end()) {
        if (Narrowed.empty()) {
          Unchecked = Refinement.next(Certified);
          if (Narrow == Certified.DeepApplication) {
            UncheckedValues = candidateValues(Module, *Query, Candidate);
            UncheckedApplication = shownApplication(
                Module, *Certified.DeepApplication, Candidate, checkLimits());
            UncheckedReason = Certified.Detail;
          }
        }
        Narrowed.push_back(Narrow);
        continue;
      }
    }
    RefinementDecision Decision = Refinement.next(Certified);
    if (Decision.Next == RefinementDecision::Action::Report) {
      Result.Status = VerifyStatus::Failed;
      Result.Reason = VerifyReason::Counterexample;
      Result.CertifiedWith = Certified.Evidence;
      return Result;
    }
    if (Decision.Next == RefinementDecision::Action::Stop) {
      if (!Narrowed.empty() && Decision.Reason == VerifyReason::SpecFuel)
        return unchecked();
      Result.Reason = Decision.Reason;
      Result.Message = Decision.Message;
      Result.InductionOnly = Decision.InductionOnly;
      return Result;
    }
    Instances.insert(Instances.end(), Decision.Instances.begin(),
                     Decision.Instances.end());
  }
}

VerifyResult CVC5VerifyBackend::verifyObligation(const ObligationModule &Module,
                                                 const Obligation &Item) const {
  VerifyResult Result = verifyQuery(Module, Item.CounterexampleQuery.get());
  Result.ObligationId = Item.StableId.empty() ? Item.Id : Item.StableId;
  Result.ObligationType = Item.Kind;
  Result.Location = Item.Loc;
  Result.Source = Item.Source;
  if (Result.Status == VerifyStatus::Unresolved)
    Result.Message = "proof obligation " + Result.ObligationId +
                     (Result.Message.empty() ? "" : ": " + Result.Message);
  return Result;
}

std::vector<VerifyResult>
CVC5VerifyBackend::verifyObligations(const ObligationModule &Module) const {
  VerifyResult Limited = querySizeLimitResult(Module, MaxQueryNodes, "cvc5");
  if (Limited.Reason != VerifyReason::None)
    return {std::move(Limited)};
  std::vector<VerifyResult> Results;
  Results.reserve(Module.Obligations.size());
  if (Jobs == 1 || Module.Obligations.size() < 2) {
    for (const Obligation &Item : Module.Obligations)
      Results.push_back(verifyObligation(Module, Item));
    return Results;
  }
  std::optional<llvm::StdThreadPool> OwnPool;
  if (!Pool)
    OwnPool.emplace(llvm::heavyweight_hardware_concurrency(Jobs));
  llvm::ThreadPoolTaskGroup Group(Pool ? *Pool : *OwnPool);
  std::vector<std::shared_future<VerifyResult>> Futures;
  Futures.reserve(Module.Obligations.size());
  for (size_t I = 0; I != Module.Obligations.size(); ++I)
    Futures.push_back(Group.async([this, &Module, I] {
      return verifyObligation(Module, Module.Obligations[I]);
    }));
  Group.wait();
  for (std::shared_future<VerifyResult> &Future : Futures)
    Results.push_back(Future.get());
  return Results;
}

VerifyResult CVC5VerifyBackend::verifyModule(const ObligationModule &Module) {
  VerifyResult Limited = querySizeLimitResult(Module, MaxQueryNodes, "cvc5");
  if (Limited.Reason != VerifyReason::None)
    return Limited;
  if (Module.Obligations.empty())
    return verifyQuery(Module, Module.CounterexampleQuery.get());
  std::vector<VerifyResult> Results = verifyObligations(Module);
  std::optional<VerifyResult> FirstFailure;
  std::optional<VerifyResult> FirstUnresolved;
  for (VerifyResult &Result : Results) {
    if (Result.Status == VerifyStatus::Failed && !FirstFailure)
      FirstFailure = std::move(Result);
    else if (Result.Status == VerifyStatus::Unresolved &&
             (!FirstUnresolved ||
              (FirstUnresolved->Reason != VerifyReason::SpecFuel &&
               Result.Reason == VerifyReason::SpecFuel)))
      FirstUnresolved = std::move(Result);
    else if (Result.Status != VerifyStatus::Verified &&
             Result.Status != VerifyStatus::Failed &&
             Result.Status != VerifyStatus::Unresolved) {
      VerifyResult Invalid;
      Invalid.Status = VerifyStatus::Unresolved;
      Invalid.Reason = VerifyReason::InvalidBackendResult;
      Invalid.Message = "cvc5 obligation returned an invalid status";
      Invalid.BackendName = "cvc5";
      return Invalid;
    }
  }
  if (FirstFailure)
    return std::move(*FirstFailure);
  if (FirstUnresolved) {
    return std::move(*FirstUnresolved);
  }
  VerifyResult Result;
  Result.Status = VerifyStatus::Verified;
  Result.BackendName = "cvc5";
  return Result;
}
