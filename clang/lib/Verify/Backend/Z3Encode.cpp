//===--- Z3Encode.cpp -----------------------------------------------------===//
#include "Z3Encode.h"
#include "ObligationSerialization.h"
#include "ObligationSimplify.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/ThreadPool.h"
#include "llvm/Support/Threading.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>
#include <cassert>
#include <z3_api.h>

using namespace clang;
using namespace verify;

namespace {

// Increment when a Z3 encoding change can invalidate a previously memoized
// successful verdict without changing the canonical semantic hash format.
constexpr unsigned Z3ProofCacheAdapterVersion = 1;

std::optional<VerifyResult> querySizeLimitResult(const ObligationModule &Module,
                                                 uint64_t MaxQueryNodes) {
  if (MaxQueryNodes == 0 || obligationModuleNodeCount(Module) <= MaxQueryNodes)
    return std::nullopt;
  VerifyResult Result;
  Result.Status = VerifyStatus::Unresolved;
  Result.Reason = VerifyReason::QuerySizeLimit;
  Result.Message = "canonical obligation module exceeds query node budget " +
                   std::to_string(MaxQueryNodes);
  Result.BackendName = "z3";
  return Result;
}

std::optional<std::string> sourceModelValue(const z3::expr &Value,
                                            const LogicSort &Sort) {
  if (Sort.Kind == LogicSortKind::Bool) {
    if (Value.is_true())
      return "true";
    if (Value.is_false())
      return "false";
    return std::nullopt;
  }

  std::string Numeral;
  if (!Value.is_numeral(Numeral))
    return std::nullopt;
  if (Sort.Kind != LogicSortKind::BitVector)
    return Numeral;
  if (Sort.BitWidth == 0)
    return std::nullopt;
  llvm::APInt Bits(Sort.BitWidth, Numeral, 10);
  llvm::SmallString<64> Decimal;
  Bits.toString(Decimal, 10, Sort.Signedness == LogicSignedness::Signed);
  return std::string(Decimal);
}

bool containsQuantifier(const VCExpr *E) {
  if (!E)
    return false;
  if (E->K == VCExpr::Forall || E->K == VCExpr::Exists)
    return true;
  return std::any_of(E->Children.begin(), E->Children.end(),
                     [](const std::unique_ptr<VCExpr> &Child) {
                       return containsQuantifier(Child.get());
                     });
}

void collectBinderNames(const VCExpr *Expression,
                        std::set<std::string> &Names) {
  if (!Expression)
    return;
  if (Expression->K == VCExpr::Forall || Expression->K == VCExpr::Exists)
    Names.insert(Expression->Binder);
  for (const auto &Child : Expression->Children)
    collectBinderNames(Child.get(), Names);
}

void collectSpecCalls(const VCExpr *Expression,
                      std::vector<const VCExpr *> &Calls) {
  if (!Expression)
    return;
  if (Expression->K == VCExpr::SpecCall)
    Calls.push_back(Expression);
  for (const auto &Child : Expression->Children)
    collectSpecCalls(Child.get(), Calls);
}

void collectModelVariables(const VCExpr *Expression,
                           std::set<std::string> Bound,
                           std::map<std::string, LogicSort> &Variables) {
  if (!Expression)
    return;
  if (Expression->K == VCExpr::Var && !Bound.count(Expression->Name) &&
      Expression->Sort.Kind != LogicSortKind::Heap) {
    Variables.emplace(Expression->Name, Expression->Sort);
    return;
  }
  if ((Expression->K == VCExpr::Forall || Expression->K == VCExpr::Exists) &&
      Expression->Children.size() == 3) {
    collectModelVariables(Expression->Children[0].get(), Bound, Variables);
    collectModelVariables(Expression->Children[1].get(), Bound, Variables);
    Bound.insert(Expression->Binder);
    collectModelVariables(Expression->Children[2].get(), std::move(Bound),
                          Variables);
    return;
  }
  for (const auto &Child : Expression->Children)
    collectModelVariables(Child.get(), Bound, Variables);
}

} // namespace

Z3Encoder::Z3Encoder() : Ctx(), Solver(Ctx) {}

z3::sort Z3Encoder::intSort() { return Ctx.int_sort(); }
z3::sort Z3Encoder::bvSort(unsigned BitWidth) { return Ctx.bv_sort(BitWidth); }
z3::sort Z3Encoder::boolSort() { return Ctx.bool_sort(); }
z3::sort Z3Encoder::heapSort() { return Ctx.array_sort(intSort(), intSort()); }

z3::sort Z3Encoder::valueSort(const LogicSort &Sort) {
  if (Sort.Kind == LogicSortKind::Bool)
    return boolSort();
  if (Sort.Kind == LogicSortKind::Pointer ||
      Sort.Kind == LogicSortKind::MathematicalInteger)
    return intSort();
  if (Sort.Kind == LogicSortKind::BitVector)
    return integerMode() ? intSort() : bvSort(Sort.BitWidth);
  if (Sort.Kind == LogicSortKind::Heap)
    return heapSort();
  markEncodingFailure("unsupported logical value sort");
  return intSort();
}

z3::func_decl Z3Encoder::specFuncDecl(const LogicFunctionDecl &Function) {
  auto It = SpecFuncDecls.find(Function.Identity);
  if (It != SpecFuncDecls.end())
    return It->second;
  std::vector<z3::sort> Domain;
  for (const LogicFunctionParameter &Parameter : Function.Parameters)
    Domain.push_back(valueSort(Parameter.Sort));
  z3::sort Ret = valueSort(Function.ResultSort);
  const std::string Name = "spec$" + Function.Identity;
  z3::func_decl F =
      Ctx.function(Name.c_str(), Domain.size(), Domain.data(), Ret);
  SpecFuncDecls.emplace(Function.Identity, F);
  return F;
}

z3::expr Z3Encoder::coerceToSort(z3::expr E, const LogicSort &Target,
                                 bool IsSigned) {
  if (Target.Kind == LogicSortKind::BitVector) {
    if (E.is_int())
      return z3::int2bv(Target.BitWidth, E);
    return E;
  }
  if (Target.Kind == LogicSortKind::MathematicalInteger ||
      Target.Kind == LogicSortKind::Pointer) {
    if (E.is_bv())
      return z3::bv2int(E, IsSigned);
    return E;
  }
  if (Target.Kind == LogicSortKind::Bool)
    return asBool(E);
  return E;
}

z3::expr Z3Encoder::heapVar(const std::string &Name) {
  auto It = Vars.find(Name);
  if (It != Vars.end())
    return It->second;
  z3::expr H = Ctx.constant(Name.c_str(), heapSort());
  Vars.emplace(Name, H);
  return H;
}

void Z3Encoder::markEncodingFailure(std::string Message) {
  if (EncodingFailed)
    return;
  EncodingFailed = true;
  EncodingError = std::move(Message);
}

z3::expr Z3Encoder::fallbackValue(const VCExpr *E) {
  if (E && E->Sort.Kind == LogicSortKind::Bool)
    return Ctx.bool_val(false);
  if (E && E->Sort.Kind == LogicSortKind::BitVector)
    return integerMode() ? Ctx.int_val(0) : Ctx.bv_val(0, E->Sort.BitWidth);
  if (E && E->Sort.Kind == LogicSortKind::Heap)
    return Ctx.constant("__cppverify_invalid_heap", heapSort());
  return Ctx.int_val(0);
}

z3::expr Z3Encoder::asBool(z3::expr E) {
  if (E.is_bool())
    return E;
  if (E.is_int())
    return E != 0;
  if (E.is_bv())
    return E != 0;
  markEncodingFailure("non-scalar expression used as a condition");
  return Ctx.bool_val(false);
}

/// Heap model is Array Int Int; pointer/index args may be bit-vectors.
static z3::expr heapIndex(z3::expr Ptr) {
  if (Ptr.is_bv())
    return z3::bv2int(Ptr, true);
  return Ptr;
}

static z3::expr heapCellValue(z3::expr Val) {
  if (Val.is_bv())
    return z3::bv2int(Val, false);
  if (Val.is_bool())
    return z3::ite(Val, Val.ctx().int_val(1), Val.ctx().int_val(0));
  return Val;
}

static bool isSignedSort(const LogicSort &Sort) {
  return Sort.Signedness == LogicSignedness::Signed;
}

static bool isIntegerLogicSort(const LogicSort &Sort) {
  return Sort.Kind == LogicSortKind::MathematicalInteger ||
         Sort.Kind == LogicSortKind::Pointer;
}

z3::expr Z3Encoder::powerOfTwo(unsigned Exponent) {
  llvm::SmallString<64> Decimal;
  llvm::APInt::getOneBitSet(Exponent + 1, Exponent)
      .toString(Decimal, 10, /*Signed=*/false);
  return Ctx.int_val(std::string(Decimal).c_str());
}

/// A decimal literal reduced into the sort's range.
z3::expr Z3Encoder::machineLiteral(llvm::StringRef Decimal,
                                   const LogicSort &Sort) {
  const unsigned Width = Sort.BitWidth;
  const unsigned Parsed =
      std::max<unsigned>(Width, static_cast<unsigned>(Decimal.size()) * 4 + 2);
  llvm::APInt Value(Parsed, Decimal, 10);
  llvm::SmallString<64> Canonical;
  Value.trunc(Width).toString(Canonical, 10, isSignedSort(Sort));
  return Ctx.int_val(std::string(Canonical).c_str());
}

/// Reduce an integer modulo 2^w into the signed or unsigned range of Sort.
z3::expr Z3Encoder::reduce(z3::expr Value, const LogicSort &Sort) {
  if (Sort.Kind != LogicSortKind::BitVector)
    return Value;
  std::string Numeral;
  if (Value.is_numeral(Numeral))
    return machineLiteral(Numeral, Sort);
  z3::expr Modulus = powerOfTwo(Sort.BitWidth);
  if (!isSignedSort(Sort))
    return z3::mod(Value, Modulus);
  z3::expr Half = powerOfTwo(Sort.BitWidth - 1);
  return z3::mod(Value + Half, Modulus) - Half;
}

z3::expr Z3Encoder::inRange(z3::expr Value, const LogicSort &Sort) {
  if (!isSignedSort(Sort))
    return Value >= Ctx.int_val(0) && Value < powerOfTwo(Sort.BitWidth);
  z3::expr Half = powerOfTwo(Sort.BitWidth - 1);
  return Value >= -Half && Value < Half;
}

/// Read the same w bits under another signedness.
z3::expr Z3Encoder::reinterpret(z3::expr Value, unsigned BitWidth,
                                bool FromSigned, bool ToSigned) {
  if (FromSigned == ToSigned)
    return Value;
  std::string Numeral;
  if (Value.is_numeral(Numeral))
    return machineLiteral(Numeral, LogicSort::bitVector(BitWidth, ToSigned));
  z3::expr Modulus = powerOfTwo(BitWidth);
  if (FromSigned)
    return z3::ite(Value < 0, Value + Modulus, Value);
  return z3::ite(Value >= powerOfTwo(BitWidth - 1), Value - Modulus, Value);
}

/// The integer counterpart of BvResize.
z3::expr Z3Encoder::convertMachine(z3::expr Value, const LogicSort &Source,
                                   const LogicSort &Target) {
  std::string Numeral;
  if (Value.is_numeral(Numeral))
    return machineLiteral(Numeral, Target);
  const bool FromSigned = isSignedSort(Source);
  const bool ToSigned = isSignedSort(Target);
  if (Target.BitWidth == Source.BitWidth)
    return reinterpret(Value, Target.BitWidth, FromSigned, ToSigned);
  if (Target.BitWidth < Source.BitWidth)
    return reduce(Value, Target);
  if (FromSigned && !ToSigned)
    return z3::ite(Value < 0, Value + powerOfTwo(Target.BitWidth), Value);
  return Value;
}

/// Cells hold the unsigned bit pattern, as in the bit-vector encoding.
z3::expr Z3Encoder::heapCell(z3::expr Value, const LogicSort &Sort) {
  if (Sort.Kind == LogicSortKind::Bool)
    return z3::ite(Value, Ctx.int_val(1), Ctx.int_val(0));
  if (Sort.Kind == LogicSortKind::BitVector)
    return reinterpret(Value, Sort.BitWidth, isSignedSort(Sort), false);
  return Value;
}

/// Names of the constants inside every non-numeral divisor of Root.
static std::set<std::string> divisorConstants(const z3::expr &Root) {
  std::set<std::string> Names;
  std::vector<std::pair<z3::expr, bool>> Work{{Root, false}};
  std::set<std::pair<unsigned, bool>> Seen;
  while (!Work.empty()) {
    auto [E, InDivisor] = Work.back();
    Work.pop_back();
    if (!Seen.insert({E.id(), InDivisor}).second)
      continue;
    if (E.is_quantifier()) {
      Work.push_back({E.body(), InDivisor});
      continue;
    }
    if (!E.is_app())
      continue;
    if (E.num_args() == 0) {
      if (InDivisor && E.decl().decl_kind() == Z3_OP_UNINTERPRETED)
        Names.insert(E.decl().name().str());
      continue;
    }
    const Z3_decl_kind Kind = E.decl().decl_kind();
    const bool Division =
        E.num_args() == 2 && (Kind == Z3_OP_DIV || Kind == Z3_OP_IDIV ||
                              Kind == Z3_OP_MOD || Kind == Z3_OP_REM);
    for (unsigned I = 0; I != E.num_args(); ++I)
      Work.push_back({E.arg(I), InDivisor || (Division && I == 1 &&
                                              !E.arg(I).is_numeral())});
  }
  return Names;
}

bool Z3Encoder::mentionsBinder(const z3::expr &Root) {
  if (BinderNames.empty())
    return false;
  std::vector<z3::expr> Work{Root};
  std::set<unsigned> Seen;
  while (!Work.empty()) {
    z3::expr E = Work.back();
    Work.pop_back();
    if (!Seen.insert(E.id()).second)
      continue;
    if (E.is_quantifier()) {
      Work.push_back(E.body());
      continue;
    }
    if (!E.is_app())
      continue;
    if (E.num_args() == 0) {
      if (E.decl().decl_kind() == Z3_OP_UNINTERPRETED &&
          BinderNames.count(E.decl().name().str()))
        return true;
      continue;
    }
    for (unsigned I = 0; I != E.num_args(); ++I)
      Work.push_back(E.arg(I));
  }
  return false;
}

/// The range guard keeps a mis-sorted term from making the query vacuous.
/// Binder-dependent terms cannot be named globally, so they keep int2bv.
z3::expr Z3Encoder::machineBits(z3::expr Value, const LogicSort &Sort) {
  const unsigned Width = Sort.BitWidth;
  const bool Signed = isSignedSort(Sort);
  std::string Numeral;
  if (Value.is_numeral(Numeral)) {
    const unsigned Parsed = std::max<unsigned>(
        Width, static_cast<unsigned>(Numeral.size()) * 4 + 2);
    llvm::SmallString<64> Pattern;
    llvm::APInt(Parsed, Numeral, 10).trunc(Width).toString(Pattern, 10, false);
    return Ctx.bv_val(std::string(Pattern).c_str(), Width);
  }
  UsedBitLevelOperation = true;
  if (!DefineBitShadows || mentionsBinder(Value))
    return z3::int2bv(Width, Value);
  const std::tuple<unsigned, unsigned, bool> Key{Value.id(), Width, Signed};
  if (auto It = BitShadows.find(Key); It != BitShadows.end())
    return It->second;
  z3::expr Bits = Ctx.bv_const(
      ("bits!" + std::to_string(BitShadows.size())).c_str(), Width);
  BitShadows.emplace(Key, Bits);
  BitDefinitions.push_back(
      z3::implies(inRange(Value, Sort), z3::bv2int(Bits, Signed) == Value));
  return Bits;
}

/// Integer mode needs the source logic sort to know how a value's bits read.
z3::expr Z3Encoder::coerce(z3::expr E, const LogicSort &Source,
                           const LogicSort &Target, bool IsSigned) {
  if (!integerMode())
    return coerceToSort(E, Target, IsSigned);
  if (Target.Kind == LogicSortKind::BitVector) {
    if (Source.Kind == LogicSortKind::BitVector) {
      if (Source.BitWidth != Target.BitWidth) {
        markEncodingFailure("bit-vector coercion changes width");
        return E;
      }
      return reinterpret(E, Target.BitWidth, isSignedSort(Source),
                         isSignedSort(Target));
    }
    if (isIntegerLogicSort(Source))
      return reduce(E, Target);
    markEncodingFailure("cannot coerce a non-integer to a bit-vector");
    return E;
  }
  if (isIntegerLogicSort(Target)) {
    if (Source.Kind == LogicSortKind::BitVector)
      return reinterpret(E, Source.BitWidth, isSignedSort(Source), IsSigned);
    return E;
  }
  if (Target.Kind == LogicSortKind::Bool)
    return asBool(E);
  return E;
}

/// C++ truncates toward zero; SMT-LIB integer division is Euclidean.
static z3::expr truncatingDivision(z3::expr L, z3::expr R) {
  z3::expr Magnitude = z3::abs(L) / z3::abs(R);
  return z3::ite((L >= 0) == (R >= 0), Magnitude, -Magnitude);
}

z3::expr Z3Encoder::integerArithOp(const VCExpr *E, z3::expr L, z3::expr R) {
  const LogicSort &Sort = E->Children[0]->Sort;
  const unsigned Width = Sort.BitWidth;
  const bool Signed = isSignedSort(Sort);
  z3::expr Zero = Ctx.int_val(0);
  // A shift amount may differ in signedness from the shifted value.
  const LogicSort &RightSort = E->Children[1]->Sort;
  auto toBits = [&](z3::expr Value, const LogicSort &OperandSort) {
    return machineBits(Value, OperandSort);
  };
  auto fromBits = [&](z3::expr Bits) { return z3::bv2int(Bits, Signed); };
  // Shift amounts are read as unsigned w-bit patterns, as in SMT-LIB.
  auto constantAmount = [&]() -> std::optional<llvm::APInt> {
    std::string Numeral;
    if (!R.is_numeral(Numeral))
      return std::nullopt;
    const unsigned Parsed = std::max<unsigned>(
        Width, static_cast<unsigned>(Numeral.size()) * 4 + 2);
    return llvm::APInt(Parsed, Numeral, 10).trunc(Width);
  };
  switch (E->K) {
  case VCExpr::Eq:
    return L == R;
  case VCExpr::Ne:
    return L != R;
  case VCExpr::Lt:
    return L < R;
  case VCExpr::Le:
    return L <= R;
  case VCExpr::Gt:
    return L > R;
  case VCExpr::Ge:
    return L >= R;
  case VCExpr::Add:
    return reduce(L + R, Sort);
  case VCExpr::Sub:
    return reduce(L - R, Sort);
  case VCExpr::Mul:
    return reduce(L * R, Sort);
  // Zero divisors follow SMT-LIB, matching the bit-vector encoding.
  case VCExpr::Div:
    if (Signed)
      return z3::ite(
          R == Zero,
          z3::ite(L >= Zero, Ctx.int_val(-1), machineLiteral("1", Sort)),
          reduce(truncatingDivision(L, R), Sort));
    return z3::ite(R == Zero, powerOfTwo(Width) - 1, L / R);
  case VCExpr::Rem:
    if (Signed)
      return z3::ite(R == Zero, L, L - R * truncatingDivision(L, R));
    return z3::ite(R == Zero, L, z3::mod(L, R));
  case VCExpr::BitAnd: {
    // x & (2^k - 1) keeps the low k bits, which is x mod 2^k in either range.
    for (auto [Value, Mask] : {std::pair{L, R}, std::pair{R, L}}) {
      std::string Numeral;
      if (!Mask.is_numeral(Numeral) ||
          llvm::StringRef(Numeral).starts_with("-"))
        continue;
      llvm::APInt Bits(Width + 1, Numeral, 10);
      if ((Bits + 1).isPowerOf2() || Bits.isZero())
        return z3::mod(Value, powerOfTwo((Bits + 1).logBase2()));
    }
    return fromBits(toBits(L, Sort) & toBits(R, RightSort));
  }
  case VCExpr::BitOr:
    return fromBits(toBits(L, Sort) | toBits(R, RightSort));
  case VCExpr::BitXor:
    return fromBits(toBits(L, Sort) ^ toBits(R, RightSort));
  case VCExpr::Shl:
  case VCExpr::Shr: {
    std::optional<llvm::APInt> Amount = constantAmount();
    if (!Amount) {
      z3::expr Bits = toBits(L, Sort);
      z3::expr Count = toBits(R, RightSort);
      if (E->K == VCExpr::Shl)
        return fromBits(z3::shl(Bits, Count));
      return fromBits(Signed ? z3::ashr(Bits, Count) : z3::lshr(Bits, Count));
    }
    if (Amount->uge(Width)) {
      if (E->K == VCExpr::Shl || !Signed)
        return Zero;
      return z3::ite(L < Zero, Ctx.int_val(-1), Zero);
    }
    const unsigned Count = static_cast<unsigned>(Amount->getZExtValue());
    if (E->K == VCExpr::Shl)
      return reduce(L * powerOfTwo(Count), Sort);
    // Arithmetic and logical right shifts are floor division by 2^k.
    return L / powerOfTwo(Count);
  }
  default:
    markEncodingFailure("unsupported machine-integer operator");
    return fallbackValue(E);
  }
}

z3::expr Z3Encoder::integerNoOverflow(const VCExpr *E,
                                      std::vector<z3::expr> Operands) {
  const LogicSort Checked =
      LogicSort::bitVector(E->Children[0]->Sort.BitWidth, /*IsSigned=*/true);
  for (unsigned I = 0; I != Operands.size(); ++I)
    Operands[I] = convertMachine(Operands[I], E->Children[I]->Sort, Checked);
  z3::expr Minimum = -powerOfTwo(Checked.BitWidth - 1);
  if (E->OverflowOp == LogicOverflowOp::Neg)
    return inRange(-Operands[0], Checked);
  if (Operands.size() != 2) {
    markEncodingFailure("binary overflow check is missing an operand");
    return Ctx.bool_val(false);
  }
  switch (E->OverflowOp) {
  case LogicOverflowOp::Add:
    return inRange(Operands[0] + Operands[1], Checked);
  case LogicOverflowOp::Sub:
    return inRange(Operands[0] - Operands[1], Checked);
  case LogicOverflowOp::Mul:
    return inRange(Operands[0] * Operands[1], Checked);
  case LogicOverflowOp::SignedDiv:
    return !(Operands[0] == Minimum && Operands[1] == -1);
  case LogicOverflowOp::Neg:
    llvm_unreachable("handled above");
  }
  llvm_unreachable("unknown overflow operation");
}

z3::expr Z3Encoder::arithOp(const VCExpr *E, z3::expr L, z3::expr R) {
  VCExpr::Kind K = E->K;
  if (L.get_sort().is_array() || R.get_sort().is_array()) {
    if (L.get_sort().is_array() && R.get_sort().is_array() && K == VCExpr::Eq)
      return L == R;
    if (L.get_sort().is_array() && R.get_sort().is_array() && K == VCExpr::Ne)
      return L != R;
    markEncodingFailure("unsupported arithmetic on heap arrays");
    return fallbackValue(E);
  }
  if (L.is_bv() && R.is_bv() &&
      L.get_sort().bv_size() != R.get_sort().bv_size()) {
    markEncodingFailure("bit-vector width mismatch");
    return fallbackValue(E);
  }
  if (!Z3_is_eq_sort(Ctx, L.get_sort(), R.get_sort())) {
    markEncodingFailure("arithmetic operand sort mismatch");
    return fallbackValue(E);
  }
  if (K != VCExpr::Eq && K != VCExpr::Ne &&
      !((L.is_int() && R.is_int()) || (L.is_bv() && R.is_bv()))) {
    markEncodingFailure("arithmetic operands are not integers");
    return fallbackValue(E);
  }
  bool IsSigned = E->Sort.Signedness == LogicSignedness::Signed;
  if (E->Sort.Kind == LogicSortKind::Bool && !E->Children.empty())
    IsSigned = E->Children[0]->Sort.Signedness == LogicSignedness::Signed;
  auto TruncatingIntDiv = [&] {
    z3::expr Zero = Ctx.int_val(0);
    z3::expr AbsL = z3::ite(L < Zero, -L, L);
    z3::expr AbsR = z3::ite(R < Zero, -R, R);
    z3::expr Magnitude = AbsL / AbsR;
    z3::expr Signed = z3::ite((L < Zero) != (R < Zero), -Magnitude, Magnitude);
    return z3::ite(R == Zero, Zero, Signed);
  };
  switch (K) {
  case VCExpr::Add:
    return L + R;
  case VCExpr::Sub:
    return L - R;
  case VCExpr::Mul:
    return L * R;
  case VCExpr::Div:
    if (L.is_int())
      return TruncatingIntDiv();
    return !IsSigned ? z3::udiv(L, R) : L / R;
  case VCExpr::Rem:
    if (L.is_int()) {
      z3::expr Zero = Ctx.int_val(0);
      z3::expr Quotient = TruncatingIntDiv();
      return z3::ite(R == Zero, L, L - Quotient * R);
    }
    return IsSigned ? z3::srem(L, R) : z3::urem(L, R);
  case VCExpr::BitAnd:
    if (L.is_bv())
      return L & R;
    break;
  case VCExpr::BitOr:
    if (L.is_bv())
      return L | R;
    break;
  case VCExpr::BitXor:
    if (L.is_bv())
      return L ^ R;
    break;
  case VCExpr::Shl:
    if (L.is_bv())
      return z3::shl(L, R);
    break;
  case VCExpr::Shr:
    if (L.is_bv())
      return IsSigned ? z3::ashr(L, R) : z3::lshr(L, R);
    break;
  case VCExpr::Lt:
    return L.is_bv() && !IsSigned ? z3::ult(L, R) : L < R;
  case VCExpr::Le:
    return L.is_bv() && !IsSigned ? z3::ule(L, R) : L <= R;
  case VCExpr::Gt:
    return L.is_bv() && !IsSigned ? z3::ugt(L, R) : L > R;
  case VCExpr::Ge:
    return L.is_bv() && !IsSigned ? z3::uge(L, R) : L >= R;
  case VCExpr::Eq:
    return L == R;
  case VCExpr::Ne:
    return L != R;
  default:
    markEncodingFailure("unsupported arithmetic operator");
    return fallbackValue(E);
  }
  markEncodingFailure("bitwise operands are not bit-vectors");
  return fallbackValue(E);
}

z3::expr
Z3Encoder::encodeVCNode(const VCExpr *E,
                        const std::map<const VCExpr *, z3::expr> &Done) {
  auto child = [&](unsigned I) -> z3::expr {
    return Done.at(E->Children[I].get());
  };
  switch (E->K) {
  case VCExpr::True:
    return Ctx.bool_val(true);
  case VCExpr::False:
    return Ctx.bool_val(false);
  case VCExpr::BoolLit:
    return Ctx.bool_val(E->BoolVal);
  case VCExpr::IntLit: {
    if (E->Sort.Kind == LogicSortKind::Pointer)
      return Ctx.int_val(E->IntVal.c_str());
    if (E->Sort.Kind == LogicSortKind::BitVector)
      return integerMode() ? machineLiteral(E->IntVal, E->Sort)
                           : Ctx.bv_val(E->IntVal.c_str(), E->Sort.BitWidth);
    if (E->Sort.Kind != LogicSortKind::MathematicalInteger) {
      markEncodingFailure("integer literal has non-integer logic sort");
      return fallbackValue(E);
    }
    return Ctx.int_val(E->IntVal.c_str());
  }
  case VCExpr::Var: {
    auto It = Vars.find(E->Name);
    if (It != Vars.end())
      return It->second;
    z3::expr Z = Ctx.int_const("_unused");
    if (E->Sort.Kind == LogicSortKind::Heap) {
      Z = Ctx.constant(E->Name.c_str(), heapSort());
    } else if (E->Sort.Kind == LogicSortKind::Bool) {
      Z = Ctx.bool_const(E->Name.c_str());
    } else if (E->Sort.Kind == LogicSortKind::Pointer ||
               E->Sort.Kind == LogicSortKind::MathematicalInteger) {
      Z = Ctx.int_const(E->Name.c_str());
    } else if (E->Sort.Kind == LogicSortKind::BitVector) {
      if (integerMode()) {
        Z = Ctx.int_const(E->Name.c_str());
        MachineVariables.emplace(E->Name, E->Sort);
      } else {
        Z = Ctx.bv_const(E->Name.c_str(), E->Sort.BitWidth);
      }
    } else {
      markEncodingFailure("unsupported variable sort: " + E->Name);
      Z = Ctx.int_const(E->Name.c_str());
    }
    Vars.emplace(E->Name, Z);
    return Z;
  }
  case VCExpr::IntToBv: {
    z3::expr Inner = child(0);
    if (integerMode())
      return reduce(Inner, E->Sort);
    if (Inner.is_int())
      return z3::int2bv(E->Sort.BitWidth, Inner);
    if (Inner.is_bv())
      return Inner;
    markEncodingFailure("cannot convert non-integer expression to bit-vector");
    return fallbackValue(E);
  }
  case VCExpr::BvResize: {
    z3::expr Inner = child(0);
    if (integerMode())
      return convertMachine(Inner, E->Children[0]->Sort, E->Sort);
    if (Inner.is_int())
      Inner = z3::int2bv(E->Children[0]->Sort.BitWidth, Inner);
    if (!Inner.is_bv()) {
      markEncodingFailure("cannot resize non-bit-vector expression");
      return fallbackValue(E);
    }
    unsigned SourceWidth = Inner.get_sort().bv_size();
    if (SourceWidth == E->Sort.BitWidth)
      return Inner;
    if (SourceWidth < E->Sort.BitWidth) {
      unsigned Extra = E->Sort.BitWidth - SourceWidth;
      return E->Children[0]->Sort.Signedness == LogicSignedness::Signed
                 ? z3::sext(Inner, Extra)
                 : z3::zext(Inner, Extra);
    }
    return Inner.extract(E->Sort.BitWidth - 1, 0);
  }
  case VCExpr::BvToInt: {
    z3::expr Inner = child(0);
    // The canonical integer already is the value under the source signedness.
    if (integerMode())
      return Inner;
    if (Inner.is_bv())
      return z3::bv2int(Inner, E->Children[0]->Sort.Signedness ==
                                   LogicSignedness::Signed);
    if (Inner.is_int())
      return Inner;
    markEncodingFailure("cannot convert " + Inner.get_sort().to_string() +
                        " expression to integer");
    return fallbackValue(E);
  }
  case VCExpr::Not:
    return !asBool(child(0));
  case VCExpr::And: {
    z3::expr_vector Ch(Ctx);
    for (const auto &C : E->Children) {
      if (!C)
        markEncodingFailure("null operand in conjunction");
      else
        Ch.push_back(asBool(Done.at(C.get())));
    }
    if (Ch.empty())
      return Ctx.bool_val(true);
    if (Ch.size() == 1)
      return Ch[0];
    return z3::mk_and(Ch);
  }
  case VCExpr::Or: {
    z3::expr_vector Ch(Ctx);
    for (const auto &C : E->Children) {
      if (!C)
        markEncodingFailure("null operand in disjunction");
      else
        Ch.push_back(asBool(Done.at(C.get())));
    }
    if (Ch.empty())
      return Ctx.bool_val(false);
    if (Ch.size() == 1)
      return Ch[0];
    return z3::mk_or(Ch);
  }
  case VCExpr::Ite: {
    z3::expr C = asBool(child(0));
    const bool IsSigned = E->Sort.Signedness == LogicSignedness::Signed;
    z3::expr T = coerce(child(1), E->Children[1]->Sort, E->Sort, IsSigned);
    z3::expr F = coerce(child(2), E->Children[2]->Sort, E->Sort, IsSigned);
    return z3::ite(C, T, F);
  }
  case VCExpr::Eq:
  case VCExpr::Ne:
  case VCExpr::Lt:
  case VCExpr::Le:
  case VCExpr::Gt:
  case VCExpr::Ge:
  case VCExpr::Add:
  case VCExpr::Sub:
  case VCExpr::Mul:
  case VCExpr::Div:
  case VCExpr::Rem:
  case VCExpr::BitAnd:
  case VCExpr::BitOr:
  case VCExpr::BitXor:
  case VCExpr::Shl:
  case VCExpr::Shr: {
    if (integerMode() &&
        E->Children[0]->Sort.Kind == LogicSortKind::BitVector) {
      z3::expr L = child(0);
      z3::expr R = child(1);
      // Folding keeps the mask and constant-shift fast paths available.
      if (L.is_numeral() && R.is_numeral())
        return integerArithOp(E, L, R).simplify();
      return integerArithOp(E, L, R);
    }
    return arithOp(E, child(0), child(1));
  }
  case VCExpr::Neg:
    if (integerMode() && E->Sort.Kind == LogicSortKind::BitVector) {
      z3::expr Value = child(0);
      if (Value.is_numeral())
        return reduce((-Value).simplify(), E->Sort);
      return reduce(-Value, E->Sort);
    }
    return -child(0);
  case VCExpr::BitNot: {
    z3::expr Value = child(0);
    // ~x is -x - 1 on two's-complement bits, which stays in either range.
    if (integerMode()) {
      if (E->Sort.Kind != LogicSortKind::BitVector) {
        markEncodingFailure("bitwise complement operand is not a bit-vector");
        return fallbackValue(E);
      }
      z3::expr Complement = isSignedSort(E->Sort)
                                ? -Value - 1
                                : powerOfTwo(E->Sort.BitWidth) - 1 - Value;
      return Value.is_numeral() ? Complement.simplify() : Complement;
    }
    if (!Value.is_bv()) {
      markEncodingFailure("bitwise complement operand is not a bit-vector");
      return fallbackValue(E);
    }
    return ~Value;
  }
  case VCExpr::NoOverflow: {
    if (E->Children.empty() ||
        E->Children[0]->Sort.Kind != LogicSortKind::BitVector) {
      markEncodingFailure("malformed overflow check");
      return Ctx.bool_val(false);
    }
    if (integerMode()) {
      std::vector<z3::expr> Operands;
      for (unsigned I = 0; I != E->Children.size(); ++I)
        Operands.push_back(child(I));
      return integerNoOverflow(E, std::move(Operands));
    }
    const unsigned BitWidth = E->Children[0]->Sort.BitWidth;
    auto Operand = [&](unsigned Index) {
      z3::expr Value = child(Index);
      if (Value.is_int())
        Value = z3::int2bv(BitWidth, Value);
      if (!Value.is_bv()) {
        markEncodingFailure("overflow-check operand is not an integer");
        return Ctx.bv_val(0, BitWidth);
      }
      const unsigned Width = Value.get_sort().bv_size();
      if (Width < BitWidth)
        return E->Children[Index]->Sort.Signedness == LogicSignedness::Signed
                   ? z3::sext(Value, BitWidth - Width)
                   : z3::zext(Value, BitWidth - Width);
      if (Width > BitWidth)
        return Value.extract(BitWidth - 1, 0);
      return Value;
    };

    z3::expr Lhs = Operand(0);
    if (E->OverflowOp == LogicOverflowOp::Neg)
      return z3::bvneg_no_overflow(Lhs);
    if (E->Children.size() != 2) {
      markEncodingFailure("binary overflow check is missing an operand");
      return Ctx.bool_val(false);
    }
    z3::expr Rhs = Operand(1);
    switch (E->OverflowOp) {
    case LogicOverflowOp::Add:
      return z3::bvadd_no_overflow(Lhs, Rhs, true) &&
             z3::bvadd_no_underflow(Lhs, Rhs);
    case LogicOverflowOp::Sub:
      return z3::bvsub_no_overflow(Lhs, Rhs) &&
             z3::bvsub_no_underflow(Lhs, Rhs, true);
    case LogicOverflowOp::Mul:
      return z3::bvmul_no_overflow(Lhs, Rhs, true) &&
             z3::bvmul_no_underflow(Lhs, Rhs);
    case LogicOverflowOp::SignedDiv:
      return z3::bvsdiv_no_overflow(Lhs, Rhs);
    case LogicOverflowOp::Neg:
      llvm_unreachable("handled above");
    }
    llvm_unreachable("unknown overflow operation");
  }
  case VCExpr::ValidPtr: {
    z3::expr Ptr = child(0);
    if (!Ptr.is_int()) {
      markEncodingFailure("pointer validity requires an integer address");
      return Ctx.bool_val(false);
    }
    auto It = SpecFuncDecls.find("__cppverify_valid_ptr");
    if (It == SpecFuncDecls.end()) {
      z3::sort Domain[] = {intSort()};
      z3::func_decl Valid =
          Ctx.function("__cppverify_valid_ptr", 1, Domain, boolSort());
      It = SpecFuncDecls.emplace("__cppverify_valid_ptr", Valid).first;
    }
    return It->second(Ptr);
  }
  case VCExpr::Select: {
    z3::expr Heap = child(0);
    z3::expr Index = heapIndex(child(1));
    if (!Heap.is_array()) {
      markEncodingFailure("heap load requires an array, got " +
                          Heap.get_sort().to_string());
      return fallbackValue(E);
    }
    if (!Index.is_int()) {
      markEncodingFailure("heap load requires an integer address, got " +
                          Index.get_sort().to_string());
      return fallbackValue(E);
    }
    z3::expr Val = z3::select(Heap, Index);
    if (E->Sort.Kind == LogicSortKind::Bool) {
      if (Val.is_bool())
        return Val;
      if (Val.is_int())
        return Val != 0;
      markEncodingFailure("boolean heap load requires an integer cell, got " +
                          Val.get_sort().to_string());
      return Ctx.bool_val(false);
    }
    if (E->Sort.Kind == LogicSortKind::Pointer)
      return Val;
    // A cell holds an arbitrary integer; its w low bits are the value.
    if (integerMode() && E->Sort.Kind == LogicSortKind::BitVector)
      return reduce(Val, E->Sort);
    return coerceToSort(Val, E->Sort,
                        E->Sort.Signedness == LogicSignedness::Signed);
  }
  case VCExpr::Store: {
    z3::expr Before = child(0);
    z3::expr Ptr = heapIndex(child(1));
    z3::expr Val = integerMode() ? heapCell(child(2), E->Children[2]->Sort)
                                 : heapCellValue(child(2));
    z3::expr After = child(3);
    return (After == z3::store(Before, Ptr, Val));
  }
  case VCExpr::Forall:
  case VCExpr::Exists: {
    z3::expr ExpectedBound = Ctx.int_const(E->Binder.c_str());
    z3::expr Bound = ExpectedBound;
    if (auto It = Vars.find(E->Binder); It != Vars.end()) {
      if (!Z3_is_eq_sort(Ctx, It->second.get_sort(),
                         ExpectedBound.get_sort())) {
        markEncodingFailure("quantifier binder sort mismatch: " + E->Binder);
        return Ctx.bool_val(false);
      }
      Bound = It->second;
    }
    z3::expr Lo = child(0);
    z3::expr Hi = child(1);
    if (!Lo.is_int() || !Hi.is_int()) {
      markEncodingFailure("quantifier bounds must be mathematical integers");
      return Ctx.bool_val(false);
    }
    z3::expr Range = (Lo <= Bound) && (Bound < Hi);
    z3::expr NonEmpty = Lo < Hi;
    z3::expr Body = asBool(child(2));
    z3::expr SimplifiedBody = Body.simplify();
    if (SimplifiedBody.is_true()) {
      Vars.erase(E->Binder);
      return E->K == VCExpr::Forall ? Ctx.bool_val(true) : NonEmpty;
    }
    if (SimplifiedBody.is_false()) {
      Vars.erase(E->Binder);
      return E->K == VCExpr::Exists ? Ctx.bool_val(false) : !NonEmpty;
    }
    z3::expr_vector Binders(Ctx);
    Binders.push_back(Bound);
    Vars.erase(E->Binder);
    if (E->K == VCExpr::Forall)
      return z3::forall(Binders, z3::implies(Range, Body));
    return z3::exists(Binders, Range && Body);
  }
  case VCExpr::SpecCall: {
    auto It = LogicFunctions.find(E->SpecCallee);
    if (It == LogicFunctions.end() || !It->second) {
      markEncodingFailure("missing spec definition: " + E->SpecCallee);
      return fallbackValue(E);
    }
    const LogicFunctionDecl &Function = *It->second;
    if (E->Children.size() != Function.Parameters.size()) {
      markEncodingFailure("spec argument count mismatch: " + E->SpecCallee);
      return fallbackValue(E);
    }
    z3::func_decl F = specFuncDecl(Function);
    std::vector<z3::expr> Args;
    for (unsigned i = 0; i < E->Children.size(); ++i) {
      z3::expr Arg = coerce(
          child(i), E->Children[i]->Sort, Function.Parameters[i].Sort,
          Function.Parameters[i].Sort.Signedness == LogicSignedness::Signed);
      Args.push_back(std::move(Arg));
    }
    z3::expr A = F(static_cast<unsigned>(Args.size()), Args.data());
    // Opaque applications are integer functions; keep them in range.
    if (integerMode())
      A = reduce(A, Function.ResultSort);
    return coerce(A, Function.ResultSort, E->Sort,
                  Function.ResultSort.Signedness == LogicSignedness::Signed);
  }
  }
  markEncodingFailure("unsupported verification expression");
  return fallbackValue(E);
}

z3::expr Z3Encoder::encodeVC(const VCExpr *Root) {
  if (!Root) {
    markEncodingFailure("null verification expression");
    return Ctx.bool_val(false);
  }
  std::map<const VCExpr *, z3::expr> Done;
  std::vector<const VCExpr *> Stack = {Root};
  while (!Stack.empty()) {
    const VCExpr *E = Stack.back();
    if (Done.count(E)) {
      Stack.pop_back();
      continue;
    }
    if ((E->K == VCExpr::Forall || E->K == VCExpr::Exists) &&
        !Vars.count(E->Binder)) {
      z3::expr Bound = Ctx.int_const(E->Binder.c_str());
      Vars.emplace(E->Binder, std::move(Bound));
    }
    bool Pending = false;
    for (const auto &C : E->Children) {
      if (C && !Done.count(C.get())) {
        Stack.push_back(C.get());
        Pending = true;
        break;
      }
    }
    if (Pending)
      continue;
    Stack.pop_back();
    z3::expr Enc = encodeVCNode(E, Done);
    Done.insert({E, std::move(Enc)});
  }
  return Done.at(Root);
}

void Z3Encoder::emitSpecCallAxiom(const VCExpr *Call) {
  if (!Call || Call->K != VCExpr::SpecCall)
    return;
  auto It = LogicFunctions.find(Call->SpecCallee);
  if (It == LogicFunctions.end() || !It->second) {
    markEncodingFailure("missing spec definition: " + Call->SpecCallee);
    return;
  }
  const LogicFunctionDecl &Function = *It->second;
  if (Function.DefinitionLevels.empty())
    return;
  if (Call->Children.size() != Function.Parameters.size()) {
    markEncodingFailure("spec argument count mismatch: " +
                        Function.DisplayName);
    return;
  }

  std::vector<z3::expr> Args;
  for (unsigned I = 0; I < Call->Children.size(); ++I) {
    z3::expr Arg = encodeVC(Call->Children[I].get());
    Arg = coerce(Arg, Call->Children[I]->Sort, Function.Parameters[I].Sort,
                 Function.Parameters[I].Sort.Signedness ==
                     LogicSignedness::Signed);
    Args.push_back(std::move(Arg));
  }

  std::vector<std::pair<std::string, std::optional<z3::expr>>> SavedVars;
  for (unsigned I = 0; I < Function.Parameters.size() && I < Args.size(); ++I) {
    const std::string &ParamName = Function.Parameters[I].Name;
    auto Existing = Vars.find(ParamName);
    SavedVars.emplace_back(ParamName,
                           Existing == Vars.end()
                               ? std::optional<z3::expr>()
                               : std::optional<z3::expr>(Existing->second));
    Vars.erase(ParamName);
    Vars.emplace(ParamName, Args[I]);
  }

  z3::func_decl Fdecl = specFuncDecl(Function);
  z3::expr LHS = Fdecl(static_cast<unsigned>(Args.size()), Args.data());
  for (const auto &Definition : Function.DefinitionLevels) {
    z3::expr RHS = encodeVC(Definition.get());
    RHS = coerce(RHS, Definition->Sort, Function.ResultSort,
                 Function.ResultSort.Signedness == LogicSignedness::Signed);
    Solver.add(LHS == RHS);
  }

  for (auto &Saved : SavedVars) {
    Vars.erase(Saved.first);
    if (Saved.second)
      Vars.emplace(Saved.first, *Saved.second);
  }
}

std::optional<z3::expr> Z3Encoder::encodeModule(const ObligationModule &Module,
                                                const LogicExpr *Query,
                                                VerifyResult &Result) {
  ActiveEncoding = IntegerEncoding == MachineIntegerEncoding::BitVector
                       ? MachineIntegerEncoding::BitVector
                       : MachineIntegerEncoding::Integer;
  std::optional<z3::expr> Encoded = encodeModuleAs(Module, Query, Result);
  if (!Encoded || IntegerEncoding != MachineIntegerEncoding::Auto ||
      !UsedBitLevelOperation)
    return Encoded;
  ActiveEncoding = MachineIntegerEncoding::BitVector;
  return encodeModuleAs(Module, Query, Result);
}

z3::expr_vector Z3Encoder::rangeFacts() {
  z3::expr_vector Facts(Ctx);
  for (const auto &[Name, Sort] : MachineVariables)
    Facts.push_back(inRange(Ctx.int_const(Name.c_str()), Sort));
  return Facts;
}

std::optional<z3::expr>
Z3Encoder::encodeModuleAs(const ObligationModule &Module,
                          const LogicExpr *Query, VerifyResult &Result) {
  if (!Query)
    Query = Module.CounterexampleQuery.get();
  Vars.clear();
  Solver = containsQuantifier(Query) ? z3::tactic(Ctx, "smt").mk_solver()
                                     : z3::solver(Ctx);
  z3::params Params(Ctx);
  if (TimeoutMs > 0)
    Params.set("timeout", TimeoutMs);
  if (ResourceLimit > 0)
    Params.set("rlimit", ResourceLimit);
  Params.set("mbqi", true);
  Params.set("qi.eager_threshold", 0.0);
  Solver.set(Params);
  EncodingFailed = false;
  EncodingError.clear();
  LogicFunctions.clear();
  SpecFuncDecls.clear();
  ModelVariables.clear();
  MachineVariables.clear();
  BinderNames.clear();
  BitShadows.clear();
  BitDefinitions.clear();
  UsedBitLevelOperation = false;
  for (const auto &[Identity, Function] : Module.LogicFunctions)
    LogicFunctions.emplace(Identity, &Function);
  if (!Query) {
    Result.Status = VerifyStatus::Unresolved;
    Result.Reason = VerifyReason::MissingQuery;
    Result.Message = "missing counterexample query";
    return std::nullopt;
  }
  collectModelVariables(Query, {}, ModelVariables);
  collectBinderNames(Query, BinderNames);
  for (const auto &[Identity, Function] : Module.LogicFunctions)
    for (const auto &Definition : Function.DefinitionLevels)
      collectBinderNames(Definition.get(), BinderNames);
  std::vector<const VCExpr *> SpecCalls;
  collectSpecCalls(Query, SpecCalls);
  DefineBitShadows = true;
  for (const VCExpr *Call : SpecCalls)
    emitSpecCallAxiom(Call);
  Vars.clear();
  z3::expr EncodedGoal = encodeVC(Query);
  DefineBitShadows = false;
  if (EncodingFailed) {
    Result.Status = VerifyStatus::Unresolved;
    Result.Reason = VerifyReason::EncodingFailure;
    Result.Message = EncodingError;
    return std::nullopt;
  }
  return EncodedGoal;
}

namespace {
constexpr uint64_t SpecTruthSteps = 2000000;
constexpr unsigned SpecTruthDepth = 2000;
constexpr int64_t SpecTruthInstances = 100000;
constexpr unsigned SpecRefinementRounds = 64;
} // namespace

struct Z3Encoder::SpecTruth {
  explicit SpecTruth(z3::model Model) : Model(std::move(Model)) {}
  z3::model Model;
  /// Declaration of each logical function by its Z3 symbol.
  std::map<std::string, const LogicFunctionDecl *> Functions;
  std::map<std::string, z3::expr> Values;
  /// Applications whose model value differs from the true value.
  std::vector<std::pair<z3::expr, z3::expr>> Disagreements;
  std::set<std::string> Disputed;
  uint64_t Steps = SpecTruthSteps;
  unsigned Depth = 0;
};

std::optional<z3::expr> Z3Encoder::evalTrue(SpecTruth &Truth,
                                            const z3::expr &E) {
  if (Truth.Steps == 0)
    return std::nullopt;
  --Truth.Steps;
  if (E.is_numeral() || E.is_true() || E.is_false())
    return E;
  if (E.is_quantifier())
    return evalQuantifier(Truth, E);
  if (!E.is_app())
    return std::nullopt;
  const z3::func_decl Decl = E.decl();
  const Z3_decl_kind Kind = Decl.decl_kind();
  auto isBool = [](const std::optional<z3::expr> &V) {
    return V && (V->is_true() || V->is_false());
  };
  // Connectives evaluate lazily: an untaken branch may apply a function
  // outside its domain of recursion.
  if (Kind == Z3_OP_ITE) {
    std::optional<z3::expr> Cond = evalTrue(Truth, E.arg(0));
    if (!isBool(Cond))
      return std::nullopt;
    return evalTrue(Truth, E.arg(Cond->is_true() ? 1 : 2));
  }
  if (Kind == Z3_OP_AND || Kind == Z3_OP_OR) {
    const bool Deciding = Kind == Z3_OP_OR;
    bool Undetermined = false;
    for (unsigned I = 0; I < E.num_args(); ++I) {
      std::optional<z3::expr> V = evalTrue(Truth, E.arg(I));
      if (!isBool(V))
        Undetermined = true;
      else if (V->is_true() == Deciding)
        return Ctx.bool_val(Deciding);
    }
    if (Undetermined)
      return std::nullopt;
    return Ctx.bool_val(!Deciding);
  }
  if (Kind == Z3_OP_IMPLIES) {
    std::optional<z3::expr> Premise = evalTrue(Truth, E.arg(0));
    if (isBool(Premise) && Premise->is_false())
      return Ctx.bool_val(true);
    std::optional<z3::expr> Conclusion = evalTrue(Truth, E.arg(1));
    if (!isBool(Premise) || !isBool(Conclusion))
      return std::nullopt;
    return Ctx.bool_val(Conclusion->is_true());
  }
  z3::expr_vector Args(Ctx);
  for (unsigned I = 0; I < E.num_args(); ++I) {
    std::optional<z3::expr> V = evalTrue(Truth, E.arg(I));
    if (!V)
      return std::nullopt;
    Args.push_back(*V);
  }
  if (Kind == Z3_OP_UNINTERPRETED && E.num_args() > 0) {
    auto It = Truth.Functions.find(Decl.name().str());
    if (It != Truth.Functions.end() && It->second->DefinitionFuel > 0) {
      std::optional<z3::expr> True = applyTrue(Truth, *It->second, Args);
      if (!True)
        return std::nullopt;
      z3::expr Applied = Decl(Args);
      z3::expr Claimed = Truth.Model.eval(Applied, true).simplify();
      if (!z3::eq(Claimed, True->simplify())) {
        Truth.Disagreements.emplace_back(Applied, *True);
        Truth.Disputed.insert(It->second->DisplayName.empty()
                                  ? It->second->Identity
                                  : It->second->DisplayName);
      }
      return True;
    }
  }
  return Truth.Model.eval(Decl(Args), true);
}

std::optional<z3::expr> Z3Encoder::evalQuantifier(SpecTruth &Truth,
                                                  const z3::expr &Q) {
  if (!(Q.is_forall() || Q.is_exists()) ||
      Z3_get_quantifier_num_bound(Ctx, Q) != 1)
    return std::nullopt;
  // The shape the encoder emits: forall x. lo <= x < hi => P, and
  // exists x. (lo <= x < hi) && P, with lo and hi free of x.
  const bool Forall = Q.is_forall();
  z3::expr Body = Q.body();
  if (!Body.is_app() ||
      Body.decl().decl_kind() != (Forall ? Z3_OP_IMPLIES : Z3_OP_AND) ||
      Body.num_args() != 2)
    return std::nullopt;
  z3::expr Range = Body.arg(0);
  if (!Range.is_app() || Range.decl().decl_kind() != Z3_OP_AND ||
      Range.num_args() != 2 || !Range.arg(0).is_app() ||
      !Range.arg(1).is_app() || Range.arg(0).decl().decl_kind() != Z3_OP_LE ||
      Range.arg(1).decl().decl_kind() != Z3_OP_LT ||
      !Range.arg(0).arg(1).is_var() || !Range.arg(1).arg(0).is_var())
    return std::nullopt;
  std::optional<z3::expr> Lo = evalTrue(Truth, Range.arg(0).arg(0));
  std::optional<z3::expr> Hi = evalTrue(Truth, Range.arg(1).arg(1));
  int64_t Low = 0, High = 0;
  if (!Lo || !Hi || !Lo->is_numeral_i64(Low) || !Hi->is_numeral_i64(High))
    return std::nullopt;
  if (High > Low && High - Low > SpecTruthInstances)
    return std::nullopt;
  bool Undetermined = false;
  for (int64_t I = Low; I < High; ++I) {
    z3::expr_vector Value(Ctx);
    Value.push_back(Ctx.int_val(I));
    std::optional<z3::expr> V = evalTrue(Truth, Body.arg(1).substitute(Value));
    if (!V || !(V->is_true() || V->is_false()))
      Undetermined = true;
    else if (V->is_true() != Forall)
      return Ctx.bool_val(!Forall);
  }
  if (Undetermined)
    return std::nullopt;
  return Ctx.bool_val(Forall);
}

std::optional<z3::expr> Z3Encoder::applyTrue(SpecTruth &Truth,
                                             const LogicFunctionDecl &Function,
                                             const z3::expr_vector &Args) {
  if (!Function.StepDefinition || Args.size() != Function.Parameters.size() ||
      Truth.Depth >= SpecTruthDepth)
    return std::nullopt;
  std::string Key = Function.Identity;
  for (unsigned I = 0; I < Args.size(); ++I)
    Key += "\x1f" + Args[I].to_string();
  if (auto It = Truth.Values.find(Key); It != Truth.Values.end())
    return It->second;

  // Unfold one step at the argument values, as a call-site axiom does.
  std::vector<std::pair<std::string, std::optional<z3::expr>>> Saved;
  for (unsigned I = 0; I < Args.size(); ++I) {
    const std::string &Name = Function.Parameters[I].Name;
    auto Existing = Vars.find(Name);
    Saved.emplace_back(Name, Existing == Vars.end()
                                 ? std::optional<z3::expr>()
                                 : std::optional<z3::expr>(Existing->second));
    Vars.erase(Name);
    Vars.emplace(Name, Args[I]);
  }
  const bool SavedFailure = EncodingFailed;
  std::string SavedError = EncodingError;
  EncodingFailed = false;
  z3::expr Body =
      coerce(encodeVC(Function.StepDefinition.get()),
             Function.StepDefinition->Sort, Function.ResultSort,
             Function.ResultSort.Signedness == LogicSignedness::Signed);
  const bool Failed = EncodingFailed;
  EncodingFailed = SavedFailure;
  EncodingError = std::move(SavedError);
  for (auto &[Name, Value] : Saved) {
    Vars.erase(Name);
    if (Value)
      Vars.emplace(Name, *Value);
  }
  if (Failed)
    return std::nullopt;
  ++Truth.Depth;
  std::optional<z3::expr> Value = evalTrue(Truth, Body);
  --Truth.Depth;
  if (Value)
    Truth.Values.emplace(Key, *Value);
  return Value;
}

z3::check_result Z3Encoder::refineSpecModel(const ObligationModule &Module,
                                            const z3::expr &Semantics,
                                            z3::check_result Result,
                                            VerifyResult &Out) {
  if (Result != z3::sat)
    return Result;
  const std::vector<std::string> Frontier = specFrontier(Module);
  if (Frontier.empty())
    return Result;
  for (unsigned Round = 0; Result == z3::sat; ++Round) {
    SpecTruth Truth(Solver.get_model());
    for (const auto &[Identity, Function] : LogicFunctions)
      Truth.Functions.emplace(specFuncDecl(*Function).name().str(), Function);
    std::optional<z3::expr> Holds = evalTrue(Truth, Semantics);
    if (Holds && Holds->is_true())
      return Result;
    const bool Refutable =
        Holds && Holds->is_false() && !Truth.Disagreements.empty();
    if (!Refutable || Round == SpecRefinementRounds) {
      const std::set<std::string> &Names =
          Truth.Disputed.empty()
              ? std::set<std::string>(Frontier.begin(), Frontier.end())
              : Truth.Disputed;
      std::string List;
      for (const std::string &Name : Names)
        List += (List.empty() ? "" : ", ") + Name;
      Out.Status = VerifyStatus::Unresolved;
      Out.Reason = VerifyReason::SpecFuel;
      Out.Message =
          (!Refutable ? "the counterexample could not be checked against the "
                        "definition of " +
                            List
                      : "every counterexample found applies " + List +
                            " beyond its unfolding fuel and is refuted by its "
                            "definition") +
          "; raise reveal_with_fuel, bound the argument, or state a lemma";
      return z3::unknown;
    }
    // The definitions are true, so adding them at the disputed points can
    // only remove spurious models.
    for (const auto &[Applied, Value] : Truth.Disagreements)
      Solver.add(Applied == Value);
    Result = Solver.check();
  }
  return Result;
}

VerifyResult Z3Encoder::verifyModule(const ObligationModule &Module,
                                     const LogicExpr *Query,
                                     std::optional<uint64_t> TraceEventCount) {
  VerifyResult Out;
  const bool IsCompleteQuery = Query == nullptr;
  auto EncodedGoal = encodeModule(Module, Query, Out);
  if (!EncodedGoal)
    return Out;
  Solver.add(*EncodedGoal);
  for (const z3::expr &Definition : BitDefinitions)
    Solver.add(Definition);
  z3::expr Semantics = z3::mk_and(Solver.assertions());
  Solver.add(rangeFacts());
  const z3::check_result Checked =
      refineSpecModel(Module, Semantics, Solver.check(), Out);
  if (Out.Reason == VerifyReason::SpecFuel)
    return Out;
  switch (Checked) {
  case z3::unsat:
    Out.Status = VerifyStatus::Verified;
    return Out;
  case z3::sat: {
    Out.Status = VerifyStatus::Failed;
    Out.Reason = VerifyReason::Counterexample;
    z3::model Mod = Solver.get_model();
    // Range facts assign every machine variable; report those the goal does
    // not depend on as unknown. Divisor variables stay assigned (slow eval).
    z3::expr_vector Assigned(Ctx), Unassigned(Ctx);
    std::set<std::string> Freed;
    if (integerMode()) {
      const std::set<std::string> InDivisors = divisorConstants(Semantics);
      for (const auto &[Name, Sort] : MachineVariables) {
        if (InDivisors.count(Name))
          continue;
        Assigned.push_back(Ctx.int_const(Name.c_str()));
        Unassigned.push_back(Ctx.int_const(("free!" + Name).c_str()));
        z3::expr Holds = Mod.eval(Semantics.substitute(Assigned, Unassigned),
                                  /*model_completion=*/false);
        if (Holds.is_true()) {
          Freed.insert(Name);
          continue;
        }
        Assigned.pop_back();
        Unassigned.pop_back();
      }
    }
    // A diagnostic term dividing by a freed variable is undetermined.
    auto modelValue = [&](z3::expr Encoded) {
      if (Freed.empty())
        return Mod.eval(Encoded, false);
      z3::expr Substituted = Encoded.substitute(Assigned, Unassigned);
      for (const std::string &Name : divisorConstants(Encoded))
        if (Freed.count(Name))
          return Substituted;
      return Mod.eval(Substituted, false);
    };
    auto evaluate = [&](const LogicExpr *Expr) -> std::optional<std::string> {
      if (!Expr)
        return std::nullopt;
      const bool SavedFailure = EncodingFailed;
      std::string SavedError = EncodingError;
      EncodingFailed = false;
      EncodingError.clear();
      z3::expr Encoded = encodeVC(Expr);
      if (EncodingFailed) {
        EncodingFailed = SavedFailure;
        EncodingError = std::move(SavedError);
        return std::nullopt;
      }
      z3::expr Evaluated = modelValue(Encoded);
      EncodingFailed = SavedFailure;
      EncodingError = std::move(SavedError);
      return sourceModelValue(Evaluated, Expr->Sort);
    };
    if (IsCompleteQuery && !TraceEventCount) {
      for (const Obligation &Item : Module.Obligations) {
        std::optional<std::string> Fails =
            evaluate(Item.CounterexampleQuery.get());
        if (!Fails || *Fails != "true")
          continue;
        Out.ObligationId = Item.StableId.empty() ? Item.Id : Item.StableId;
        Out.ObligationType = Item.Kind;
        Out.Location = Item.Loc;
        Out.Source = Item.Source;
        TraceEventCount = Item.TraceEventCount;
        break;
      }
    }
    for (const auto &[Name, Sort] : ModelVariables) {
      auto Metadata = Module.DiagnosticVariables.find(Name);
      if (!Module.DiagnosticVariables.empty() &&
          Metadata == Module.DiagnosticVariables.end())
        continue;
      VerifyModelValue Value;
      Value.DisplayName = Metadata == Module.DiagnosticVariables.end()
                              ? Name
                              : Metadata->second.DisplayName;
      Value.InternalName = Name;
      Value.Sort = Sort;
      if (Metadata != Module.DiagnosticVariables.end()) {
        const LogicSort &Declared = Metadata->second.Sort;
        if (Declared.Kind != Sort.Kind || Declared.BitWidth != Sort.BitWidth ||
            Declared.Signedness != Sort.Signedness) {
          Out.Status = VerifyStatus::Unresolved;
          Out.Reason = VerifyReason::InvalidObligation;
          Out.Message = "diagnostic metadata sort does not match " + Name;
          Out.Model.clear();
          return Out;
        }
        Value.Source = Metadata->second.Source;
      }
      if (auto It = Vars.find(Name); It != Vars.end()) {
        z3::expr Evaluated = modelValue(It->second);
        if (!z3::eq(Evaluated, It->second))
          Value.Value = sourceModelValue(Evaluated, Sort);
      }
      Out.Model.push_back(std::move(Value));
    }
    if (TraceEventCount) {
      const uint64_t Count =
          std::min<uint64_t>(*TraceEventCount, Module.TraceEvents.size());
      for (uint64_t I = 0; I != Count; ++I) {
        const DiagnosticTraceEvent &Event = Module.TraceEvents[I];
        std::optional<std::string> Guard = evaluate(Event.Guard.get());
        if (Guard && *Guard == "false")
          continue;
        VerifyTraceEvent Trace;
        Trace.Kind = Event.Kind;
        Trace.Message = Event.Message;
        Trace.Source = Event.Source;
        if (Guard)
          Trace.Active = *Guard == "true";
        for (const DiagnosticTraceValue &Value : Event.Values)
          Trace.Values.push_back(
              {Value.Label, Value.Value->Sort, evaluate(Value.Value.get())});
        Out.Trace.push_back(std::move(Trace));
      }
    }
    return Out;
  }
  default:
    Out.Status = VerifyStatus::Unresolved;
    Out.Message = Solver.reason_unknown();
    llvm::StringRef Reason = llvm::StringRef(Out.Message).trim();
    if (TimeoutMs > 0 && Reason.equals_insensitive("timeout"))
      Out.Reason = VerifyReason::SolverTimeout;
    else if (ResourceLimit > 0 && Reason.contains_insensitive("resource limit"))
      Out.Reason = VerifyReason::SolverResourceLimit;
    else
      Out.Reason = VerifyReason::SolverUnknown;
    return Out;
  }
}

VerifyResult Z3Encoder::lowerModule(const ObligationModule &Module,
                                    llvm::raw_ostream *OS) {
  VerifyResult Out;
  auto EncodedGoal =
      encodeModule(Module, Module.CounterexampleQuery.get(), Out);
  if (!EncodedGoal)
    return Out;
  if (OS) {
    z3::expr_vector Facts = rangeFacts();
    for (unsigned I = 0; I != Facts.size(); ++I)
      *OS << Facts[I].to_string() << "\n";
    for (const z3::expr &Definition : BitDefinitions)
      *OS << Definition.to_string() << "\n";
    *OS << EncodedGoal->to_string() << "\n";
  }
  Out.Status = VerifyStatus::Lowered;
  return Out;
}

VerifyResult
verify::lowerObligationModule(const ObligationModule &Module,
                              llvm::raw_ostream *Z3Out,
                              const BackendExecutionOptions &Execution) {
  if (auto Limit = querySizeLimitResult(Module, Execution.MaxQueryNodes))
    return std::move(*Limit);
  Z3Encoder Encoder;
  Encoder.setTimeoutMs(Execution.SolverTimeoutMs);
  Encoder.setResourceLimit(Execution.SolverResourceLimit);
  Encoder.setIntegerEncoding(Execution.IntegerEncoding);
  VerifyResult Result = Encoder.lowerModule(Module, Z3Out);
  Result.BackendName = "z3";
  return Result;
}

static VerifyResult finishZ3Result(VerifyResult Result) {
  if (Result.Status != VerifyStatus::Failed)
    return Result;
  std::string Message;
  for (const VerifyModelValue &Value : Result.Model) {
    if (!Message.empty())
      Message += ", ";
    Message += Value.DisplayName;
    if (Value.DisplayName != Value.InternalName)
      Message += " [ssa=" + Value.InternalName + "]";
    Message += " [type=" + formatLogicSort(Value.Sort) +
               "] = " + Value.Value.value_or("<unknown>");
  }
  auto traceKind = [](DiagnosticTraceKind Kind) {
    switch (Kind) {
    case DiagnosticTraceKind::Branch:
      return "branch";
    case DiagnosticTraceKind::Call:
      return "call";
    case DiagnosticTraceKind::Loop:
      return "loop";
    case DiagnosticTraceKind::HeapWrite:
      return "heap-write";
    case DiagnosticTraceKind::Allocation:
      return "allocation";
    case DiagnosticTraceKind::LifetimeEnd:
      return "lifetime-end";
    case DiagnosticTraceKind::Deallocation:
      return "deallocation";
    case DiagnosticTraceKind::Return:
      return "return";
    }
    return "branch";
  };
  if (!Result.Trace.empty()) {
    if (!Message.empty())
      Message += "; ";
    Message += "trace: ";
    bool First = true;
    for (const VerifyTraceEvent &Event : Result.Trace) {
      if (!First)
        Message += " -> ";
      First = false;
      Message += traceKind(Event.Kind);
      if (!Event.Message.empty())
        Message += "." + Event.Message;
      if (Event.Source.isValid())
        Message += "@" + std::to_string(Event.Source.Line) + ":" +
                   std::to_string(Event.Source.Column);
      if (!Event.Active)
        Message += "?";
      for (const VerifyTraceValue &Value : Event.Values)
        Message += " " + Value.Label + "=" + Value.Value.value_or("<unknown>");
    }
  }
  Result.Message = std::move(Message);
  return Result;
}

std::vector<VerifyResult>
Z3VerifyBackend::verifyObligations(const ObligationModule &Module,
                                   bool StopAtFailure) {
  if (auto Limit = querySizeLimitResult(Module, MaxQueryNodes))
    return {std::move(*Limit)};

  std::vector<VerifyResult> Results;
  Results.reserve(Module.Obligations.size());
  std::vector<std::string> CacheHashes;
  std::vector<std::string> QueryHashes;
  std::vector<ProofCacheLookup> CacheLookups;
  if (Cache) {
    CacheHashes.reserve(Module.Obligations.size());
    CacheLookups.reserve(Module.Obligations.size());
    for (const Obligation &Item : Module.Obligations) {
      CacheHashes.push_back(obligationSemanticHash(Module, Item));
      CacheLookups.push_back(Cache->lookup(CacheHashes.back()));
    }
  }
  if (ReuseVerifiedQueries) {
    QueryHashes.reserve(Module.Obligations.size());
    for (const Obligation &Item : Module.Obligations)
      QueryHashes.push_back(obligationQuerySemanticHash(Module, Item));
  }
  auto IsReused = [&](size_t I) {
    return ReuseVerifiedQueries && VerifiedQueries.count(QueryHashes[I]) != 0;
  };
  if (Jobs == 1 || Module.Obligations.size() < 2) {
    for (size_t I = 0; I != Module.Obligations.size(); ++I) {
      Results.push_back(verifyObligation(
          Module, Module.Obligations[I],
          Cache ? llvm::StringRef(CacheHashes[I]) : llvm::StringRef(),
          Cache ? &CacheLookups[I] : nullptr, IsReused(I)));
      if (StopAtFailure && Results.back().Status == VerifyStatus::Failed)
        break;
    }
  } else {
    llvm::StdThreadPool Pool(llvm::heavyweight_hardware_concurrency(Jobs));
    std::vector<std::shared_future<VerifyResult>> Futures;
    Futures.reserve(Module.Obligations.size());
    for (size_t I = 0; I != Module.Obligations.size(); ++I) {
      Futures.push_back(Pool.async(
          [this, &Module, &CacheHashes, &CacheLookups, &IsReused, I] {
            return verifyObligation(
                Module, Module.Obligations[I],
                Cache ? llvm::StringRef(CacheHashes[I]) : llvm::StringRef(),
                Cache ? &CacheLookups[I] : nullptr, IsReused(I));
          }));
    }
    for (std::shared_future<VerifyResult> &Future : Futures)
      Results.push_back(Future.get());
  }
  if (ReuseVerifiedQueries)
    for (size_t I = 0; I != Results.size(); ++I)
      if (Results[I].Status == VerifyStatus::Verified)
        VerifiedQueries.insert(QueryHashes[I]);
  if (Cache) {
    if (llvm::Error Error = Cache->prune()) {
      std::string Message = llvm::toString(std::move(Error));
      if (Results.empty()) {
        VerifyResult Result;
        Result.Status = VerifyStatus::Unresolved;
        Result.Reason = VerifyReason::CacheIOFailure;
        Result.Message = Message;
        Result.BackendName = "z3";
        Results.push_back(std::move(Result));
      } else {
        ++Results.front().CacheErrors;
        Results.front().CacheError = std::move(Message);
      }
    }
  }
  return Results;
}

Z3VerifyBackend::Z3VerifyBackend(const BackendExecutionOptions &Execution,
                                 llvm::StringRef CacheBackendName,
                                 bool ReuseVerifiedQueries)
    : TimeoutMs(Execution.SolverTimeoutMs),
      ResourceLimit(Execution.SolverResourceLimit), Jobs(Execution.Jobs),
      MaxQueryNodes(Execution.MaxQueryNodes),
      IntegerEncoding(Execution.IntegerEncoding),
      SkipWholeModuleRetry(Execution.SkipWholeModuleRetry),
      ReuseVerifiedQueries(ReuseVerifiedQueries) {
  Enc.setTimeoutMs(TimeoutMs);
  Enc.setResourceLimit(ResourceLimit);
  Enc.setIntegerEncoding(IntegerEncoding);
  if (!Execution.ProofCachePath.empty()) {
    std::string Identity =
        CacheBackendName.str() + ";adapter=cppverify-z3-v" +
        std::to_string(Z3ProofCacheAdapterVersion) +
        ";ints=" + machineIntegerEncodingName(IntegerEncoding).str() +
        ";solver=" + std::string(Z3_get_full_version());
    Cache = std::make_unique<ProofCache>(
        Execution.ProofCachePath, std::move(Identity),
        Execution.ProofCacheMaxBytes, Execution.ProofCacheMaxEntries);
  }
}

VerifyResult Z3VerifyBackend::verifyObligation(const ObligationModule &Module,
                                               const Obligation &Item,
                                               llvm::StringRef SemanticHash,
                                               const ProofCacheLookup *Lookup,
                                               bool Reused) {
  VerifyResult Result;
  if (Reused) {
    Result.Status = VerifyStatus::Verified;
    Result.BackendName = "z3";
    Result.ReusedQueries = 1;
  } else if (Cache) {
    assert(Lookup && !SemanticHash.empty() && "cache lookup was not prepared");
    if (Lookup->Kind == ProofCacheLookupKind::Hit) {
      Result.Status = VerifyStatus::Verified;
      Result.BackendName = "z3";
      Result.CacheHits = 1;
    } else if (Lookup->Kind == ProofCacheLookupKind::Corrupt ||
               Lookup->Kind == ProofCacheLookupKind::IOFailure) {
      Result.Status = VerifyStatus::Unresolved;
      Result.Reason = Lookup->Kind == ProofCacheLookupKind::Corrupt
                          ? VerifyReason::CacheCorrupt
                          : VerifyReason::CacheIOFailure;
      Result.Message = Lookup->Message;
      Result.CacheErrors = 1;
      Result.CacheError = Lookup->Message;
    } else {
      Result.CacheMisses = 1;
    }
  }

  if (Result.Status != VerifyStatus::Verified &&
      Result.Reason != VerifyReason::CacheCorrupt &&
      Result.Reason != VerifyReason::CacheIOFailure) {
    Z3Encoder Encoder;
    Encoder.setTimeoutMs(TimeoutMs);
    Encoder.setResourceLimit(ResourceLimit);
    Encoder.setIntegerEncoding(IntegerEncoding);
    Result = Encoder.verifyModule(Module, Item.CounterexampleQuery.get(),
                                  Item.TraceEventCount);
    if (Cache)
      Result.CacheMisses = 1;
    if (Cache && Result.Status == VerifyStatus::Verified) {
      if (llvm::Error Error = Cache->store(SemanticHash)) {
        Result.CacheErrors = 1;
        Result.CacheError = llvm::toString(std::move(Error));
      }
    }
  }

  Result.ObligationId = Item.StableId.empty() ? Item.Id : Item.StableId;
  Result.ObligationType = Item.Kind;
  Result.Location = Item.Loc;
  Result.Source = Item.Source;
  if (Result.Status == VerifyStatus::Unresolved)
    Result.Message = "proof obligation " + Result.ObligationId +
                     (Result.Message.empty() ? "" : ": " + Result.Message);
  return finishZ3Result(std::move(Result));
}

/// Internal IDs of the obligations that one-to-one Results did not prove.
static std::optional<std::vector<std::string>>
unprovedObligations(const ObligationModule &Module,
                    const std::vector<VerifyResult> &Results) {
  if (Results.size() != Module.Obligations.size())
    return std::nullopt;
  std::vector<std::string> Unproved;
  for (size_t I = 0; I != Results.size(); ++I)
    if (Results[I].Status != VerifyStatus::Verified)
      Unproved.push_back(Module.Obligations[I].Id);
  return Unproved;
}

VerifyResult Z3VerifyBackend::verifyModule(const ObligationModule &Module) {
  if (auto Limit = querySizeLimitResult(Module, MaxQueryNodes))
    return std::move(*Limit);
  if (Jobs != 1 || Cache) {
    std::vector<VerifyResult> Results = verifyObligations(Module);
    std::optional<std::vector<std::string>> Unproved =
        unprovedObligations(Module, Results);
    uint64_t Hits = 0;
    uint64_t Misses = 0;
    uint64_t Errors = 0;
    uint64_t Reused = 0;
    std::string CacheError;
    std::optional<VerifyResult> FirstUnresolved;
    std::optional<VerifyResult> FirstFailure;
    for (VerifyResult &Result : Results) {
      Hits += Result.CacheHits;
      Misses += Result.CacheMisses;
      Errors += Result.CacheErrors;
      Reused += Result.ReusedQueries;
      if (CacheError.empty() && !Result.CacheError.empty())
        CacheError = Result.CacheError;
      if (Result.Status == VerifyStatus::Failed && !FirstFailure)
        FirstFailure = std::move(Result);
      else if (Result.Status == VerifyStatus::Unresolved && !FirstUnresolved)
        FirstUnresolved = std::move(Result);
    }
    VerifyResult Result;
    if (FirstFailure)
      Result = std::move(*FirstFailure);
    else if (FirstUnresolved) {
      const bool CacheFailure =
          FirstUnresolved->Reason == VerifyReason::CacheCorrupt ||
          FirstUnresolved->Reason == VerifyReason::CacheIOFailure;
      if (!CacheFailure && !SkipWholeModuleRetry) {
        VerifyResult Whole = Enc.verifyModule(Module);
        if (Whole.Status != VerifyStatus::Unresolved) {
          Result = finishZ3Result(std::move(Whole));
          if (Cache && Result.Status == VerifyStatus::Verified) {
            for (const Obligation &Item : Module.Obligations) {
              if (llvm::Error Error =
                      Cache->store(obligationSemanticHash(Module, Item))) {
                ++Errors;
                if (CacheError.empty())
                  CacheError = llvm::toString(std::move(Error));
                else
                  llvm::consumeError(std::move(Error));
              }
            }
            if (llvm::Error Error = Cache->prune()) {
              ++Errors;
              if (CacheError.empty())
                CacheError = llvm::toString(std::move(Error));
              else
                llvm::consumeError(std::move(Error));
            }
          }
        } else {
          Result = std::move(*FirstUnresolved);
        }
      } else {
        Result = std::move(*FirstUnresolved);
      }
    } else {
      Result.Status = VerifyStatus::Verified;
    }
    Result.CacheHits = Hits;
    Result.CacheMisses = Misses;
    Result.CacheErrors = Errors;
    Result.CacheError = std::move(CacheError);
    Result.ReusedQueries = Reused;
    if (Result.Status == VerifyStatus::Unresolved)
      Result.UnprovedObligations = std::move(Unproved);
    return Result;
  }

  // Spec equations often solve best as one formula. For spec-free programs,
  // use a short complete-VC probe and preserve the configured budget for the
  // ordered obligations.
  const bool WholeUsedFullBudget =
      !Module.LogicFunctions.empty() || (TimeoutMs > 0 && TimeoutMs <= 500);
  Enc.setTimeoutMs(WholeUsedFullBudget
                       ? TimeoutMs
                       : (TimeoutMs == 0 ? 500 : std::min(TimeoutMs, 500U)));
  VerifyResult Whole = Enc.verifyModule(Module);
  Enc.setTimeoutMs(TimeoutMs);
  if (Whole.Status == VerifyStatus::Verified)
    return finishZ3Result(std::move(Whole));

  if (Whole.Status == VerifyStatus::Failed) {
    bool SawUnresolved = false;
    for (VerifyResult Result :
         verifyObligations(Module, /*StopAtFailure=*/true)) {
      if (Result.Status == VerifyStatus::Verified)
        continue;
      if (Result.Status == VerifyStatus::Unresolved) {
        SawUnresolved = true;
        continue;
      }
      if (Result.Status == VerifyStatus::Failed)
        return Result;
    }
    if (SawUnresolved)
      return finishZ3Result(std::move(Whole));
    VerifyResult Inconsistent;
    Inconsistent.Status = VerifyStatus::Unresolved;
    Inconsistent.Reason = VerifyReason::InconsistentBackendResults;
    Inconsistent.Message =
        "combined query was satisfiable but every individual obligation was "
        "proved";
    return Inconsistent;
  }

  auto retryWhole = [&](VerifyResult SplitResult) {
    if (WholeUsedFullBudget || SkipWholeModuleRetry)
      return finishZ3Result(std::move(SplitResult));
    VerifyResult Retry = Enc.verifyModule(Module);
    if (Retry.Status != VerifyStatus::Unresolved)
      return finishZ3Result(std::move(Retry));
    return finishZ3Result(std::move(SplitResult));
  };

  std::vector<VerifyResult> Results =
      verifyObligations(Module, /*StopAtFailure=*/true);
  std::optional<std::vector<std::string>> Unproved =
      unprovedObligations(Module, Results);
  std::optional<VerifyResult> FirstUnresolved;
  for (VerifyResult &Result : Results) {
    if (Result.Status != VerifyStatus::Verified) {
      if (Result.Status == VerifyStatus::Unresolved) {
        if (!FirstUnresolved)
          FirstUnresolved = std::move(Result);
        continue;
      }
      return std::move(Result);
    }
  }

  if (FirstUnresolved) {
    VerifyResult Result = retryWhole(std::move(*FirstUnresolved));
    if (Result.Status == VerifyStatus::Unresolved)
      Result.UnprovedObligations = std::move(Unproved);
    return Result;
  }

  VerifyResult R;
  R.Status = VerifyStatus::Verified;
  return R;
}