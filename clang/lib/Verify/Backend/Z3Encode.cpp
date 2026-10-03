//===--- Z3Encode.cpp -----------------------------------------------------===//
#include "Z3Encode.h"
#include "ObligationSerialization.h"
#include "ObligationSimplify.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/ThreadPool.h"
#include "llvm/Support/Threading.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>
#include <cassert>
#include <chrono>
#include <condition_variable>
#include <cstdio>
#include <functional>
#include <iostream>
#include <map>
#include <mutex>
#include <set>
#include <thread>
#include <z3_api.h>
#ifdef LLVM_ON_UNIX
#include <unistd.h>
#endif

using namespace clang;
using namespace verify;

namespace {

// Increment when a Z3 encoding change can invalidate a previously memoized
// successful verdict without changing the canonical semantic hash format.
constexpr unsigned Z3ProofCacheAdapterVersion = 2;

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
  if (E->K == VCExpr::Forall || E->K == VCExpr::Exists ||
      E->K == VCExpr::HeapFrame)
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
  if (Expression->K == VCExpr::Forall || Expression->K == VCExpr::Exists) {
    for (size_t I = 0; I + 1 < Expression->Children.size(); ++I)
      collectModelVariables(Expression->Children[I].get(), Bound, Variables);
    Bound.insert(Expression->Binder);
    collectModelVariables(Expression->Children.back().get(), std::move(Bound),
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

z3::sort Z3Encoder::optionSort() {
  if (OptionSort)
    return *OptionSort;
  Z3_constructor None =
      Z3_mk_constructor(Ctx, Z3_mk_string_symbol(Ctx, "none"),
                        Z3_mk_string_symbol(Ctx, "is-none"), 0, nullptr,
                        nullptr, nullptr);
  Z3_symbol Field = Z3_mk_string_symbol(Ctx, "value");
  Z3_sort FieldSort = intSort();
  unsigned Reference = 0;
  Z3_constructor Some = Z3_mk_constructor(
      Ctx, Z3_mk_string_symbol(Ctx, "some"), Z3_mk_string_symbol(Ctx, "is-some"),
      1, &Field, &FieldSort, &Reference);
  Z3_constructor Constructors[] = {None, Some};
  Z3_sort Sort = Z3_mk_datatype(
      Ctx, Z3_mk_string_symbol(Ctx, "cppverify.option"), 2, Constructors);
  Z3_del_constructor(Ctx, None);
  Z3_del_constructor(Ctx, Some);
  Ctx.check_error();
  OptionSort = z3::sort(Ctx, Sort);
  NoneDecl = z3::func_decl(Ctx, Z3_get_datatype_sort_constructor(Ctx, Sort, 0));
  SomeDecl = z3::func_decl(Ctx, Z3_get_datatype_sort_constructor(Ctx, Sort, 1));
  IsSomeDecl =
      z3::func_decl(Ctx, Z3_get_datatype_sort_recognizer(Ctx, Sort, 1));
  OptionValueDecl = z3::func_decl(
      Ctx, Z3_get_datatype_sort_constructor_accessor(Ctx, Sort, 1, 0));
  return *OptionSort;
}

z3::sort Z3Encoder::valueSort(const LogicSort &Sort) {
  if (Sort.Kind == LogicSortKind::Bool)
    return boolSort();
  if (Sort.Kind == LogicSortKind::Seq)
    return z3::sort(Ctx, Z3_mk_seq_sort(Ctx, intSort()));
  if (Sort.Kind == LogicSortKind::Set)
    return Ctx.array_sort(intSort(), boolSort());
  if (Sort.Kind == LogicSortKind::Multiset)
    return Ctx.array_sort(intSort(), intSort());
  if (Sort.Kind == LogicSortKind::Map)
    return Ctx.array_sort(intSort(), optionSort());
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
  const bool Recursive = NativeRecursion && Function.StepDefinition;
  if (Recursive && Function.DefinitionFuel == 0)
    NativeHidden.insert(Function.DisplayName.empty() ? Function.Identity
                                                     : Function.DisplayName);
  z3::func_decl F =
      Recursive
          ? Ctx.recfun((Name + "$rec" + std::to_string(EncodingPass)).c_str(),
                       Domain.size(), Domain.data(), Ret)
          : Ctx.function(Name.c_str(), Domain.size(), Domain.data(), Ret);
  SpecFuncDecls.emplace(Function.Identity, F);
  if (Recursive)
    UndefinedRecursive.push_back(&Function);
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
  if (E && E->Sort.isCollection())
    return Ctx.constant("__cppverify_invalid_collection", valueSort(E->Sort));
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
  // A value already in range is itself; saying so keeps mod out of the
  // arithmetic whenever the solver knows the operation does not wrap.
  z3::expr Modulus = powerOfTwo(Sort.BitWidth);
  if (!isSignedSort(Sort))
    return z3::ite(inRange(Value, Sort), Value, z3::mod(Value, Modulus));
  z3::expr Half = powerOfTwo(Sort.BitWidth - 1);
  return z3::ite(inRange(Value, Sort), Value,
                 z3::mod(Value + Half, Modulus) - Half);
}

z3::expr Z3Encoder::cellValue(const z3::expr &Cell, const LogicSort &Sort) {
  std::string Numeral;
  if (Cell.is_numeral(Numeral) || !CellFunctions)
    return reduce(Cell, Sort);
  const std::string Name = std::string("cppverify.cell_") +
                           (isSignedSort(Sort) ? "i" : "u") +
                           std::to_string(Sort.BitWidth);
  auto It = CellDecls.find(Name);
  if (It == CellDecls.end()) {
    z3::func_decl Decl = Ctx.recfun(Name.c_str(), intSort(), intSort());
    z3::expr Parameter = Ctx.int_const("x");
    z3::expr_vector Parameters(Ctx);
    Parameters.push_back(Parameter);
    z3::expr Body = reduce(Parameter, Sort);
    Ctx.recdef(Decl, Parameters, Body);
    It = CellDecls
             .emplace(Name, std::make_pair(Decl, "(define-fun-rec " + Name +
                                                     " ((x Int)) Int " +
                                                     Body.to_string() + ")"))
             .first;
  }
  UsedCellDecls.insert(Name);
  return It->second.first(Cell);
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
    } else if (E->Sort.isCollection()) {
      Z = Ctx.constant(E->Name.c_str(), valueSort(E->Sort));
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
    if ((E->K == VCExpr::Eq || E->K == VCExpr::Ne) &&
        E->Children[0]->Sort.isCollection()) {
      z3::expr Equal =
          collectionEquality(E->Children[0]->Sort, child(0), child(1));
      return E->K == VCExpr::Eq ? Equal : !Equal;
    }
    return arithOp(E, child(0), child(1));
  }
  case VCExpr::Collection: {
    std::vector<z3::expr> Args;
    for (unsigned I = 0; I != E->Children.size(); ++I)
      Args.push_back(child(I));
    return encodeCollection(E, std::move(Args));
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
      return cellValue(Val, E->Sort);
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
  case VCExpr::HeapFrame: {
    // Unbounded, so that Z3's model-based instantiation can make the two
    // heaps agree by default; a bounded address range defeats it.
    z3::expr Address = Ctx.int_const("__frame_address");
    z3::expr Inside = Ctx.bool_val(false);
    for (unsigned I = 2; I + 1 < E->Children.size(); I += 2)
      Inside = Inside || (heapIndex(child(I)) <= Address &&
                          Address < heapIndex(child(I + 1)));
    return namedForall(Address,
                       Inside || z3::select(child(1), Address) ==
                                     z3::select(child(0), Address),
                       "q!frame");
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
    if (E->Children.size() == 1) {
      z3::expr_vector Binders(Ctx);
      Binders.push_back(Bound);
      z3::expr Body = asBool(child(0));
      z3::expr Quantified =
          quantify(E, E->K == VCExpr::Forall, Binders, Body);
      Vars.erase(E->Binder);
      return Quantified;
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
    z3::expr Quantified =
        E->K == VCExpr::Forall
            ? quantify(E, true, Binders, z3::implies(Range, Body))
            : quantify(E, false, Binders, Range && Body);
    Vars.erase(E->Binder);
    return Quantified;
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
    std::vector<z3::expr> Args;
    for (unsigned i = 0; i < E->Children.size(); ++i) {
      z3::expr Arg = coerce(
          child(i), E->Children[i]->Sort, Function.Parameters[i].Sort,
          Function.Parameters[i].Sort.Signedness == LogicSignedness::Signed);
      Args.push_back(std::move(Arg));
    }
    z3::expr A = inlined(Function)
                     ? inlineDefinition(Function, Args)
                     : specFuncDecl(Function)(
                           static_cast<unsigned>(Args.size()), Args.data());
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

z3::expr Z3Encoder::collectionEquality(const LogicSort &Sort,
                                       const z3::expr &L, const z3::expr &R) {
  if (Sort.Kind != LogicSortKind::Multiset)
    return L == R;
  // A cell below zero counts zero, so multisets agree count by count.
  z3::expr Element = Ctx.int_const("__multiset_element");
  auto count = [&](const z3::expr &M) {
    z3::expr Cell = z3::select(M, Element);
    return z3::ite(Cell >= 0, Cell, Ctx.int_val(0));
  };
  return namedForall(Element, count(L) == count(R), "q!multiset");
}

z3::expr Z3Encoder::encodeCollection(const VCExpr *E,
                                     std::vector<z3::expr> Args) {
  auto arg = [&](size_t I) -> z3::expr {
    if (I < Args.size())
      return Args[I];
    markEncodingFailure("collection operation lacks an operand");
    return Ctx.int_val(0);
  };
  auto wrap = [&](Z3_ast Ast) {
    z3::expr Result(Ctx, Ast);
    Ctx.check_error();
    return Result;
  };
  const z3::expr Zero = Ctx.int_val(0);
  auto length = [&](const z3::expr &S) {
    return wrap(Z3_mk_seq_length(Ctx, S));
  };
  auto extract = [&](const z3::expr &S, const z3::expr &From,
                     const z3::expr &Count) {
    return seqExtract(S, From, Count);
  };
  auto concat = [&](const z3::expr &A, const z3::expr &B) {
    Z3_ast Parts[] = {A, B};
    return wrap(Z3_mk_seq_concat(Ctx, 2, Parts));
  };
  auto unit = [&](const z3::expr &X) { return wrap(Z3_mk_seq_unit(Ctx, X)); };
  auto count = [&](const z3::expr &M, const z3::expr &X) {
    z3::expr Cell = z3::select(M, X);
    return z3::ite(Cell >= 0, Cell, Zero);
  };
  using Op = LogicCollectionOp;
  switch (E->CollectionOp) {
  case Op::SeqEmpty:
    return wrap(Z3_mk_seq_empty(Ctx, valueSort(E->Sort)));
  case Op::SeqUnit:
    return unit(arg(0));
  case Op::SeqLength:
    return length(arg(0));
  case Op::SeqIndex:
    return seqAt(arg(0), arg(1));
  case Op::SeqPush: {
    z3::expr S = arg(0), X = arg(1);
    z3::expr Pushed = concat(S, unit(X));
    indexFacts(Pushed, [&](const z3::expr &K) {
      return z3::ite(K == length(S), X, seqAt(S, K));
    });
    return Pushed;
  }
  case Op::SeqSubrange: {
    // seq.extract clamps by itself: from a start in [0, len) it stops at the
    // end, and it is empty from any other start or for a count below 1.
    // Only a negative start differs, where subrange starts at 0.
    z3::expr S = arg(0), Lo = arg(1), Hi = arg(2);
    z3::expr Range = extract(S, Lo, Hi - Lo);
    const LogicExpr *Start =
        E->Children.size() > 1 ? E->Children[1].get() : nullptr;
    if (!Start || Start->K != LogicExpr::IntLit ||
        llvm::StringRef(Start->IntVal).starts_with("-"))
      Range = z3::ite(Lo < Zero, extract(S, Zero, Hi), Range);
    z3::expr Len = length(S);
    z3::expr From = z3::ite(Lo < Zero, Zero, z3::ite(Lo > Len, Len, Lo));
    z3::expr To = z3::ite(Hi < From, From, z3::ite(Hi > Len, Len, Hi));
    indexFacts(Range, [&](const z3::expr &K) {
      return z3::ite(Zero <= K && K < To - From, seqAt(S, From + K), Zero);
    });
    return Range;
  }
  case Op::SeqConcat: {
    z3::expr A = arg(0), B = arg(1);
    z3::expr Joined = concat(A, B);
    indexFacts(Joined, [&](const z3::expr &K) {
      return z3::ite(K < length(A), seqAt(A, K), seqAt(B, K - length(A)));
    });
    return Joined;
  }
  case Op::SeqContains: {
    z3::expr S = arg(0), X = arg(1);
    z3::expr Contains = wrap(Z3_mk_seq_contains(Ctx, S, unit(X)));
    bridgeContains(Contains, S, X);
    return Contains;
  }
  case Op::SetEmpty:
    return wrap(Z3_mk_empty_set(Ctx, intSort()));
  case Op::SetInsert:
    return wrap(Z3_mk_set_add(Ctx, arg(0), arg(1)));
  case Op::SetRemove:
    return wrap(Z3_mk_set_del(Ctx, arg(0), arg(1)));
  case Op::SetContains:
    return wrap(Z3_mk_set_member(Ctx, arg(1), arg(0)));
  case Op::SetUnion: {
    Z3_ast Sets[] = {arg(0), arg(1)};
    return wrap(Z3_mk_set_union(Ctx, 2, Sets));
  }
  case Op::SetIntersect: {
    Z3_ast Sets[] = {arg(0), arg(1)};
    return wrap(Z3_mk_set_intersect(Ctx, 2, Sets));
  }
  case Op::SetDifference:
    return wrap(Z3_mk_set_difference(Ctx, arg(0), arg(1)));
  case Op::SetSubset:
    return wrap(Z3_mk_set_subset(Ctx, arg(0), arg(1)));
  case Op::MultisetEmpty:
    return z3::const_array(intSort(), Zero);
  case Op::MultisetInsert:
    return z3::store(arg(0), arg(1), count(arg(0), arg(1)) + 1);
  case Op::MultisetRemove: {
    z3::expr C = count(arg(0), arg(1));
    return z3::store(arg(0), arg(1), z3::ite(C > 0, C - 1, Zero));
  }
  case Op::MultisetCount:
    return count(arg(0), arg(1));
  case Op::MapEmpty:
    optionSort();
    return z3::const_array(intSort(), (*NoneDecl)());
  case Op::MapInsert:
    optionSort();
    return z3::store(arg(0), arg(1), (*SomeDecl)(arg(2)));
  case Op::MapRemove:
    optionSort();
    return z3::store(arg(0), arg(1), (*NoneDecl)());
  case Op::MapContains:
    optionSort();
    return (*IsSomeDecl)(z3::select(arg(0), arg(1)));
  case Op::MapGet: {
    optionSort();
    z3::expr Cell = z3::select(arg(0), arg(1));
    return z3::ite((*IsSomeDecl)(Cell), (*OptionValueDecl)(Cell), Zero);
  }
  }
  markEncodingFailure("unsupported collection operation");
  return fallbackValue(E);
}

z3::expr Z3Encoder::seqAt(const z3::expr &S, const z3::expr &K) {
  LogicSort SeqSort = LogicSort::collection(LogicSortKind::Seq);
  z3::sort Seq = valueSort(SeqSort);
  auto wrap = [&](Z3_ast Ast) {
    z3::expr Result(Ctx, Ast);
    Ctx.check_error();
    return Result;
  };
  auto length = [&](const z3::expr &X) {
    return wrap(Z3_mk_seq_length(Ctx, X));
  };
  const z3::expr Zero = Ctx.int_val(0);
  if (!SeqAtDecl) {
    // A recursive-function definition, so that models interpret it exactly.
    SeqAtDecl = Ctx.recfun("cppverify.seq_at", Seq, intSort(), intSort());
    z3::expr Sequence = Ctx.constant("cppverify!s", Seq);
    z3::expr Index = Ctx.int_const("cppverify!i");
    z3::expr_vector Parameters(Ctx);
    Parameters.push_back(Sequence);
    Parameters.push_back(Index);
    Ctx.recdef(*SeqAtDecl, Parameters,
               z3::ite(Zero <= Index && Index < length(Sequence),
                       wrap(Z3_mk_seq_nth(Ctx, Sequence, Index)), Zero));
  }
  return (*SeqAtDecl)(S, K);
}

static bool containsIte(const z3::expr &E, std::set<unsigned> &Seen) {
  if (!E.is_app() || !Seen.insert(E.id()).second)
    return false;
  if (E.decl().decl_kind() == Z3_OP_ITE)
    return true;
  for (unsigned I = 0; I != E.num_args(); ++I)
    if (containsIte(E.arg(I), Seen))
      return true;
  return false;
}

z3::expr Z3Encoder::patternable(const z3::expr &Term) {
  std::set<unsigned> Seen;
  if (!containsIte(Term, Seen))
    return Term;
  auto It = PatternNames.find(Term.id());
  if (It != PatternNames.end())
    return It->second;
  // A pattern cannot contain ite: name the closed term by a fresh constant
  // defined as it, which preserves every model.
  z3::expr Name = Ctx.constant(
      ("cppverify!t" + std::to_string(PatternNames.size())).c_str(),
      Term.get_sort());
  CollectionAxioms.push_back(Name == Term);
  return PatternNames.emplace(Term.id(), Name).first->second;
}

void Z3Encoder::indexFacts(
    const z3::expr &Term,
    llvm::function_ref<z3::expr(const z3::expr &)> Element) {
  // Only a closed term: an axiom beside the query cannot mention a binder.
  if (!SequenceFacts || mentionsBinder(Term) ||
      !IndexedTerms.insert(Term.id()).second)
    return;
  z3::expr K = Ctx.int_const("cppverify!k");
  z3::expr Read = seqAt(patternable(Term), K);
  z3::expr Body = Read == Element(K);
  CollectionAxioms.push_back(theorem(K, Read, Body, "fact!index"));
}

void Z3Encoder::bridgeContains(const z3::expr &Contains, const z3::expr &S,
                               const z3::expr &X) {
  // Only a closed term: an axiom beside the query cannot mention a binder.
  if (!SequenceFacts || mentionsBinder(Contains) ||
      !BridgedContains.insert(Contains.id()).second)
    return;
  const z3::expr Zero = Ctx.int_val(0);
  z3::expr Length(Ctx, Z3_mk_seq_length(Ctx, S));
  Ctx.check_error();
  // contains implies a read of x at some index w: a fresh witness, which
  // preserves satisfiability.
  z3::expr Witness = Ctx.int_const(
      ("cppverify!w" + std::to_string(BridgedContains.size())).c_str());
  CollectionAxioms.push_back(z3::implies(
      Contains, Zero <= Witness && Witness < Length && seqAt(S, Witness) == X));
  // A read of x at any index in range implies contains.
  z3::expr K = Ctx.int_const("cppverify!k");
  z3::expr Read = seqAt(patternable(S), K);
  z3::expr Body = z3::implies(Zero <= K && K < Length && Read == X, Contains);
  CollectionAxioms.push_back(theorem(K, Read, Body, "fact!contains"));
}

z3::expr Z3Encoder::theorem(const z3::expr &Bound, const z3::expr &Trigger,
                            const z3::expr &Body, const char *Id) {
  // A pattern is not reference counted: make it last, right before use.
  Z3_ast Term = Trigger;
  Z3_pattern Pattern = Z3_mk_pattern(Ctx, 1, &Term);
  Ctx.check_error();
  Z3_app Binder = Bound;
  z3::expr Forall(
      Ctx, Z3_mk_quantifier_const_ex(Ctx, true, 0, Z3_mk_string_symbol(Ctx, Id),
                                     Z3_mk_string_symbol(Ctx, ""), 1, &Binder,
                                     1, &Pattern, 0, nullptr, Body));
  Ctx.check_error();
  return Forall;
}

z3::expr Z3Encoder::namedForall(const z3::expr &Bound, const z3::expr &Body,
                                const char *Id) {
  Z3_app Binder = Bound;
  z3::expr Forall(
      Ctx, Z3_mk_quantifier_const_ex(Ctx, true, 0, Z3_mk_string_symbol(Ctx, Id),
                                     Z3_mk_string_symbol(Ctx, ""), 1, &Binder,
                                     0, nullptr, 0, nullptr, Body));
  Ctx.check_error();
  return Forall;
}

z3::expr Z3Encoder::seqExtract(const z3::expr &S, const z3::expr &From,
                               const z3::expr &Count) {
  auto wrap = [&](Z3_ast Ast) {
    z3::expr Result(Ctx, Ast);
    Ctx.check_error();
    return Result;
  };
  z3::expr Whole = wrap(Z3_mk_seq_extract(Ctx, S, From, Count));
  // A theorem of seq.extract, stated at this extract of a concatenation:
  // from a start i >= 0 it lies in b, in a, or across both. Z3's word
  // equations rarely find the split themselves. A quantified form would
  // leave every satisfiable query to model-based instantiation, which
  // cannot check a quantifier over sequences.
  if (!SequenceFacts || !S.is_app() ||
      S.decl().decl_kind() != Z3_OP_SEQ_CONCAT || S.num_args() != 2 ||
      mentionsBinder(Whole) || !SplitExtracts.insert(Whole.id()).second)
    return Whole;
  z3::expr A = S.arg(0);
  z3::expr B = S.arg(1);
  const z3::expr Zero = Ctx.int_val(0);
  z3::expr LengthA = wrap(Z3_mk_seq_length(Ctx, A));
  z3::expr Head = seqExtract(A, From, LengthA - From);
  z3::expr Tail = seqExtract(B, Zero, Count - (LengthA - From));
  Z3_ast Parts[] = {Head, Tail};
  z3::expr Split = z3::ite(
      From >= LengthA, seqExtract(B, From - LengthA, Count),
      z3::ite(From + Count <= LengthA, seqExtract(A, From, Count),
              wrap(Z3_mk_seq_concat(Ctx, 2, Parts))));
  CollectionAxioms.push_back(z3::implies(Zero <= From, Whole == Split));
  return Whole;
}

std::optional<z3::expr> Z3Encoder::patternTerm(const VCExpr *Term) {
  if (Term->K == VCExpr::Select && Term->Children.size() == 2)
    return z3::select(encodeVC(Term->Children[0].get()),
                      heapIndex(encodeVC(Term->Children[1].get())));
  // A collection read: the index function, or a select of the array that
  // represents a set, multiset, or map.
  if (isCollectionRead(*Term) && Term->Children.size() == 2) {
    z3::expr Collection = encodeVC(Term->Children[0].get());
    z3::expr Key = encodeVC(Term->Children[1].get());
    if (Term->CollectionOp == LogicCollectionOp::SeqIndex)
      return seqAt(Collection, Key);
    return z3::select(Collection, Key);
  }
  if (Term->K != VCExpr::SpecCall)
    return std::nullopt;
  auto It = LogicFunctions.find(Term->SpecCallee);
  if (It == LogicFunctions.end() || !It->second || inlined(*It->second) ||
      It->second->Parameters.size() != Term->Children.size())
    return std::nullopt;
  const LogicFunctionDecl &Function = *It->second;
  std::vector<z3::expr> Args;
  for (unsigned I = 0; I != Term->Children.size(); ++I)
    Args.push_back(coerce(encodeVC(Term->Children[I].get()),
                          Term->Children[I]->Sort, Function.Parameters[I].Sort,
                          Function.Parameters[I].Sort.Signedness ==
                              LogicSignedness::Signed));
  return specFuncDecl(Function)(static_cast<unsigned>(Args.size()),
                                Args.data());
}

z3::expr Z3Encoder::quantify(const VCExpr *E, bool Forall,
                             z3::expr_vector &Binders, const z3::expr &Body) {
  z3::expr_vector Terms(Ctx);
  for (const auto &Pattern : E->Patterns) {
    std::optional<z3::expr> Term = patternTerm(Pattern.get());
    if (!Term) {
      Terms.resize(0);
      break;
    }
    Terms.push_back(*Term);
  }
  std::vector<Z3_app> Bound;
  for (unsigned I = 0; I != Binders.size(); ++I)
    Bound.push_back(Binders[I]);
  std::vector<Z3_ast> TermAsts;
  for (unsigned I = 0; I != Terms.size(); ++I)
    TermAsts.push_back(Terms[I]);
  Z3_pattern Pattern = nullptr;
  if (!TermAsts.empty())
    Pattern = Z3_mk_pattern(Ctx, static_cast<unsigned>(TermAsts.size()),
                            TermAsts.data());
  const std::string Id =
      E->Source.isValid() ? "q@" + std::to_string(E->Source.Line) + ":" +
                                std::to_string(E->Source.Column)
                          : "q";
  Z3_ast Quantified = Z3_mk_quantifier_const_ex(
      Ctx, Forall, 0, Z3_mk_string_symbol(Ctx, Id.c_str()),
      Z3_mk_string_symbol(Ctx, ""), static_cast<unsigned>(Bound.size()),
      Bound.data(), Pattern ? 1 : 0, Pattern ? &Pattern : nullptr, 0, nullptr,
      Body);
  Ctx.check_error();
  return z3::expr(Ctx, Quantified);
}

std::vector<QuantifierProfileEntry>
Z3Encoder::profileQuantifiers(const z3::expr_vector &Assertions) {
  std::vector<QuantifierProfileEntry> Profile;
#ifdef LLVM_ON_UNIX
  // Z3 reports each quantifier's instantiations on stderr when its solver is
  // destroyed, so the rerun captures that descriptor; one at a time.
  static std::mutex Serial;
  std::lock_guard<std::mutex> Lock(Serial);
  llvm::SmallString<128> Path;
  int Fd = -1;
  if (llvm::sys::fs::createTemporaryFile("cppverify-qi", "txt", Fd, Path))
    return Profile;
  std::cerr.flush();
  std::fflush(stderr);
  const int Saved = ::dup(2);
  ::dup2(Fd, 2);
  {
    z3::solver Rerun = z3::tactic(Ctx, "smt").mk_solver();
    z3::params Params(Ctx);
    Params.set("timeout", TimeoutMs == 0 ? 10000U : std::min(TimeoutMs, 10000U));
    Params.set("qi.profile", true);
    Rerun.set(Params);
    for (unsigned I = 0; I != Assertions.size(); ++I)
      Rerun.add(Assertions[I]);
    (void)check(Rerun, TimeoutMs == 0 ? 10000U : std::min(TimeoutMs, 10000U));
  }
  std::cerr.flush();
  std::fflush(stderr);
  ::dup2(Saved, 2);
  ::close(Saved);
  ::close(Fd);
  auto Text = llvm::MemoryBuffer::getFile(Path);
  llvm::sys::fs::remove(Path);
  if (!Text)
    return Profile;
  // [quantifier_instances] q@LINE:COL : instances : ... : generation : cost
  llvm::SmallVector<llvm::StringRef> Lines;
  (*Text)->getBuffer().split(Lines, '\n');
  std::map<std::pair<unsigned, unsigned>, QuantifierProfileEntry> ByPosition;
  for (llvm::StringRef Line : Lines) {
    if (!Line.consume_front("[quantifier_instances]"))
      continue;
    llvm::SmallVector<llvm::StringRef> Fields;
    Line.split(Fields, ':');
    if (Fields.size() < 7)
      continue;
    QuantifierProfileEntry Entry;
    llvm::StringRef Id = Fields[0].trim();
    if (!Id.consume_front("q@") || Id.getAsInteger(10, Entry.Line) ||
        Fields[1].trim().getAsInteger(10, Entry.Column) ||
        Fields[2].trim().getAsInteger(10, Entry.Instances) ||
        Fields[5].trim().getAsInteger(10, Entry.MaxGeneration))
      continue;
    auto [It, Inserted] =
        ByPosition.emplace(std::make_pair(Entry.Line, Entry.Column), Entry);
    if (!Inserted) {
      It->second.Instances += Entry.Instances;
      It->second.MaxGeneration =
          std::max(It->second.MaxGeneration, Entry.MaxGeneration);
    }
  }
  for (const auto &[Position, Entry] : ByPosition)
    Profile.push_back(Entry);
  llvm::sort(Profile, [](const QuantifierProfileEntry &L,
                         const QuantifierProfileEntry &R) {
    return L.Instances > R.Instances;
  });
  if (Profile.size() > 5)
    Profile.resize(5);
#endif
  return Profile;
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
  if (Function.DefinitionLevels.empty() || inlined(Function))
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

z3::solver Z3Encoder::freshSolver() {
  z3::solver Fresh =
      QuantifiedQuery ? z3::tactic(Ctx, "smt").mk_solver() : z3::solver(Ctx);
  z3::params Params(Ctx);
  if (TimeoutMs > 0)
    Params.set("timeout", TimeoutMs);
  if (ResourceLimit > 0)
    Params.set("rlimit", ResourceLimit);
  Params.set("mbqi", true);
  Params.set("qi.eager_threshold", 0.0);
  Fresh.set(Params);
  return Fresh;
}

void Z3Encoder::interrupt() {
  {
    std::lock_guard<std::mutex> Guard(CheckLock);
    Stopped = true;
  }
  CheckChanged.notify_all();
  Ctx.interrupt();
}

z3::check_result Z3Encoder::check(z3::solver &S, unsigned Ms) {
  using Clock = std::chrono::steady_clock;
  {
    std::lock_guard<std::mutex> Guard(CheckLock);
    if (Stopped)
      return z3::unknown;
    CheckFinished = false;
  }
  // Z3 forgets a cancellation that arrives inside one of its nested resource
  // scopes (leaving the scope clears it), whether from its own timeout or
  // from interrupt(). A check past its time, or stopped, is therefore
  // interrupted again until it returns.
  constexpr std::chrono::milliseconds Grace(100);
  constexpr std::chrono::milliseconds Interval(50);
  bool TimedOut = false;
  bool Interrupted = false;
  std::thread Watchdog([&] {
    std::unique_lock<std::mutex> Lock(CheckLock);
    const auto Limit =
        Ms == 0 ? Clock::now() + std::chrono::hours(24 * 365)
                : Clock::now() + std::chrono::milliseconds(Ms) + Grace;
    auto Next = Limit;
    while (!CheckFinished) {
      if (Stopped || Clock::now() >= Next) {
        TimedOut = TimedOut || Clock::now() >= Limit;
        Ctx.interrupt();
        Interrupted = true;
        Next = Clock::now() + Interval;
      }
      CheckChanged.wait_until(Lock, Next);
    }
  });
  auto Join = llvm::make_scope_exit([&] {
    {
      std::lock_guard<std::mutex> Guard(CheckLock);
      CheckFinished = true;
    }
    CheckChanged.notify_all();
    Watchdog.join();
    Overran = Overran || TimedOut;
    if (Interrupted) {
      // A check opens a resource scope, which clears an interrupt left over.
      z3::solver Reset(Ctx);
      (void)Reset.check();
    }
  });
  return S.check();
}

std::optional<z3::expr>
Z3Encoder::encodeModuleAs(const ObligationModule &Module,
                          const LogicExpr *Query, VerifyResult &Result) {
  if (!Query)
    Query = Module.CounterexampleQuery.get();
  Vars.clear();
  QuantifiedQuery = containsQuantifier(Query);
  Solver = freshSolver();
  EncodingFailed = false;
  EncodingError.clear();
  LogicFunctions.clear();
  SpecFuncDecls.clear();
  UndefinedRecursive.clear();
  NativeHidden.clear();
  Inlined.clear();
  NonRecursive.clear();
  if (NativeRecursion) {
    NonRecursive = nonRecursiveDefinitions(Module);
  } else {
    // A visible non-recursive definition is exact and finite: it replaces
    // every application, under a quantifier too, as the frontend's inlining
    // does. Equations at closed applications alone left one applied to a
    // binder (in a spec's own checks, or in a fact about an application)
    // uninterpreted.
    for (const std::string &Identity : nonRecursiveDefinitions(Module))
      if (auto It = Module.LogicFunctions.find(Identity);
          It != Module.LogicFunctions.end() && It->second.DefinitionFuel > 0)
        NonRecursive.insert(Identity);
  }
  ++EncodingPass;
  ModelVariables.clear();
  MachineVariables.clear();
  BinderNames.clear();
  BitShadows.clear();
  BitDefinitions.clear();
  CollectionAxioms.clear();
  IndexedTerms.clear();
  SplitExtracts.clear();
  PatternNames.clear();
  BridgedContains.clear();
  UsedCellDecls.clear();
  CellFunctions =
      Module.RequiredFeatures & (logicFeature(LogicFeature::Sequences) |
                                 logicFeature(LogicFeature::Collections));
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
  std::unique_ptr<LogicExpr> Instantiated = instantiateAtReads(*Query);
  const LogicExpr *Goal = Instantiated ? Instantiated.get() : Query;
  if (std::unique_ptr<LogicExpr> Extensional =
          SequenceFacts ? instantiateExtensionality(*Goal) : nullptr) {
    Instantiated = std::move(Extensional);
    Goal = Instantiated.get();
    collectBinderNames(Goal, BinderNames);
  }
  std::vector<const VCExpr *> SpecCalls;
  collectSpecCalls(Goal, SpecCalls);
  DefineBitShadows = true;
  for (const VCExpr *Call : SpecCalls)
    emitSpecCallAxiom(Call);
  Vars.clear();
  z3::expr EncodedGoal = encodeVC(Goal);
  DefineBitShadows = false;
  if (NativeRecursion && !defineRecursiveFunctions())
    markEncodingFailure("cannot encode a native recursive definition");
  if (EncodingFailed) {
    Result.Status = VerifyStatus::Unresolved;
    Result.Reason = VerifyReason::EncodingFailure;
    Result.Message = EncodingError;
    return std::nullopt;
  }
  return EncodedGoal;
}

z3::expr Z3Encoder::symbol(const std::string &Name, const LogicSort &Sort) {
  if (auto It = Vars.find(Name); It != Vars.end())
    return It->second;
  if (Sort.Kind == LogicSortKind::Bool)
    return Ctx.bool_const(Name.c_str());
  if (Sort.Kind == LogicSortKind::Heap)
    return Ctx.constant(Name.c_str(), heapSort());
  if (Sort.isCollection())
    return Ctx.constant(Name.c_str(), valueSort(Sort));
  if (Sort.Kind == LogicSortKind::BitVector && !integerMode())
    return Ctx.bv_const(Name.c_str(), Sort.BitWidth);
  return Ctx.int_const(Name.c_str());
}

z3::func_decl Z3Encoder::validPointerDecl() {
  auto It = SpecFuncDecls.find("__cppverify_valid_ptr");
  if (It == SpecFuncDecls.end()) {
    z3::sort Domain[] = {intSort()};
    It = SpecFuncDecls
             .emplace(
                 "__cppverify_valid_ptr",
                 Ctx.function("__cppverify_valid_ptr", 1, Domain, boolSort()))
             .first;
  }
  return It->second;
}

z3::expr
Z3Encoder::arrayTerm(const HeapValue &Heap,
                     const std::function<z3::expr(const CertInt &)> &Cell) {
  // Single cells over the default are stores; longer runs are a lambda
  // choosing the greatest break at or below the address.
  bool PointCells = true;
  for (auto It = Heap.Breaks.begin(); It != Heap.Breaks.end(); ++It) {
    auto Next = std::next(It);
    if (It->second == Heap.Default)
      continue;
    if (Next == Heap.Breaks.end() ||
        !(Next->first == It->first + CertInt(1)) ||
        !(Next->second == Heap.Default))
      PointCells = false;
  }
  if (PointCells) {
    z3::expr Array = z3::const_array(intSort(), Cell(Heap.Default));
    for (const auto &[Address, Value] : Heap.Breaks)
      if (!(Value == Heap.Default))
        Array = z3::store(Array, Ctx.int_val(Address.toDecimal().c_str()),
                          Cell(Value));
    return Array;
  }
  z3::expr Address = Ctx.int_const("cppverify!heap_address");
  z3::expr Result = Cell(Heap.Default);
  for (const auto &[Break, Run] : Heap.Breaks)
    Result = z3::ite(Address >= Ctx.int_val(Break.toDecimal().c_str()),
                     Cell(Run), Result);
  return z3::lambda(Address, Result);
}

z3::expr Z3Encoder::valueTerm(const LogicValue &Value, const LogicSort &Sort) {
  auto integer = [&](const CertInt &I) {
    return Ctx.int_val(I.toDecimal().c_str());
  };
  switch (Value.K) {
  case LogicValue::Kind::Bool:
    return Ctx.bool_val(Value.Truth);
  case LogicValue::Kind::Heap:
  case LogicValue::Kind::Multiset:
    return arrayTerm(*Value.Heap, integer);
  case LogicValue::Kind::Set:
    return arrayTerm(*Value.Heap, [&](const CertInt &Member) {
      return Ctx.bool_val(!(Member == CertInt(0)));
    });
  case LogicValue::Kind::Map: {
    optionSort();
    z3::expr Domain = arrayTerm(*Value.Heap, integer);
    z3::expr Values = arrayTerm(*Value.Values, integer);
    z3::expr Key = Ctx.int_const("cppverify!map_key");
    return z3::lambda(Key, z3::ite(z3::select(Domain, Key) != 0,
                                   (*SomeDecl)(z3::select(Values, Key)),
                                   (*NoneDecl)()));
  }
  case LogicValue::Kind::Seq: {
    const std::vector<CertInt> &Elements = *Value.Elements;
    if (Elements.empty()) {
      z3::expr Empty(Ctx, Z3_mk_seq_empty(Ctx, valueSort(Sort)));
      Ctx.check_error();
      return Empty;
    }
    std::vector<z3::expr> Units;
    for (const CertInt &Element : Elements) {
      Units.push_back(z3::expr(Ctx, Z3_mk_seq_unit(Ctx, integer(Element))));
      Ctx.check_error();
    }
    if (Units.size() == 1)
      return Units[0];
    std::vector<Z3_ast> Parts(Units.begin(), Units.end());
    z3::expr Sequence(Ctx, Z3_mk_seq_concat(Ctx, Parts.size(), Parts.data()));
    Ctx.check_error();
    return Sequence;
  }
  case LogicValue::Kind::Integer:
    if (Sort.Kind == LogicSortKind::BitVector && !integerMode())
      return Ctx.bv_val(
          CertInt::fromBits(Value.Integer.bits(Sort.BitWidth), false)
              .toDecimal()
              .c_str(),
          Sort.BitWidth);
    return Ctx.int_val(Value.Integer.toDecimal().c_str());
  }
  llvm_unreachable("unknown logic value kind");
}

std::optional<HeapValue> Z3Encoder::heapValue(const z3::model &Model,
                                              const z3::expr &Value) {
  auto integer = [](const z3::expr &E) -> std::optional<CertInt> {
    std::string Numeral;
    if (!E.is_int() || !E.is_numeral(Numeral))
      return std::nullopt;
    return CertInt::fromDecimal(Numeral);
  };
  if (!Value.is_app())
    return piecewiseHeap(Model, Value);
  switch (Value.decl().decl_kind()) {
  case Z3_OP_CONST_ARRAY: {
    std::optional<CertInt> Default = integer(Value.arg(0));
    if (!Default)
      return std::nullopt;
    HeapValue Heap;
    Heap.Default = *Default;
    return Heap;
  }
  case Z3_OP_STORE: {
    std::optional<HeapValue> Heap = heapValue(Model, Value.arg(0));
    std::optional<CertInt> Address = integer(Value.arg(1));
    std::optional<CertInt> Cell = integer(Value.arg(2));
    if (!Heap || !Address || !Cell)
      return std::nullopt;
    Heap->set(*Address, *Cell);
    return Heap;
  }
  case Z3_OP_AS_ARRAY: {
    z3::func_decl Function(Ctx, Z3_get_as_array_func_decl(Ctx, Value));
    if (!Model.has_interp(Function))
      return std::nullopt;
    z3::func_interp Interpretation = Model.get_func_interp(Function);
    Z3_ast Else = Z3_func_interp_get_else(Ctx, Interpretation);
    if (!Else)
      return std::nullopt;
    std::optional<CertInt> Default = integer(z3::expr(Ctx, Else));
    if (!Default)
      return piecewiseHeap(Model, Value);
    HeapValue Heap;
    Heap.Default = *Default;
    for (unsigned I = 0; I != Interpretation.num_entries(); ++I) {
      z3::func_entry Entry = Interpretation.entry(I);
      if (Entry.num_args() != 1)
        return std::nullopt;
      std::optional<CertInt> Address = integer(Entry.arg(0));
      std::optional<CertInt> Cell = integer(Entry.value());
      if (!Address || !Cell)
        return std::nullopt;
      Heap.set(*Address, *Cell);
    }
    return Heap;
  }
  default:
    return piecewiseHeap(Model, Value);
  }
}

/// A model array built from comparisons of the address with numerals, as
/// model-based quantifier instantiation builds them, is constant between
/// consecutive numerals: read it at each.
std::optional<HeapValue> Z3Encoder::piecewiseHeap(
    const z3::model &Model, const z3::expr &Value,
    const std::function<std::optional<CertInt>(const z3::expr &)> &Decode) {
  std::set<std::string> Numerals;
  std::set<unsigned> Seen;
  bool Supported = true;
  std::function<void(const z3::expr &)> Scan = [&](const z3::expr &E) {
    if (!Supported || !Seen.insert(E.id()).second)
      return;
    if (E.is_var())
      return;
    if (E.is_quantifier()) {
      if (!E.is_lambda()) {
        Supported = false;
        return;
      }
      Scan(E.body());
      return;
    }
    if (!E.is_app()) {
      Supported = false;
      return;
    }
    std::string Numeral;
    if (E.is_numeral(Numeral)) {
      Numerals.insert(Numeral);
      return;
    }
    switch (E.decl().decl_kind()) {
    case Z3_OP_ITE:
    case Z3_OP_AND:
    case Z3_OP_OR:
    case Z3_OP_NOT:
    case Z3_OP_EQ:
    case Z3_OP_LE:
    case Z3_OP_LT:
    case Z3_OP_GE:
    case Z3_OP_GT:
    case Z3_OP_SELECT:
    case Z3_OP_STORE:
    case Z3_OP_CONST_ARRAY:
    case Z3_OP_TRUE:
    case Z3_OP_FALSE:
    case Z3_OP_DT_CONSTRUCTOR:
    case Z3_OP_DT_RECOGNISER:
    case Z3_OP_DT_IS:
    case Z3_OP_DT_ACCESSOR:
      break;
    case Z3_OP_AS_ARRAY:
    case Z3_OP_UNINTERPRETED: {
      z3::func_decl Function =
          E.decl().decl_kind() == Z3_OP_AS_ARRAY
              ? z3::func_decl(Ctx, Z3_get_as_array_func_decl(Ctx, E))
              : E.decl();
      if (Function.arity() == 0) {
        if (Model.has_interp(Function))
          Scan(Model.get_const_interp(Function));
      } else if (Model.has_interp(Function)) {
        z3::func_interp Interpretation = Model.get_func_interp(Function);
        for (unsigned I = 0; I != Interpretation.num_entries(); ++I) {
          z3::func_entry Entry = Interpretation.entry(I);
          for (unsigned A = 0; A != Entry.num_args(); ++A)
            Scan(Entry.arg(A));
          Scan(Entry.value());
        }
        if (Z3_ast Else = Z3_func_interp_get_else(Ctx, Interpretation))
          Scan(z3::expr(Ctx, Else));
      } else {
        Supported = false;
      }
      break;
    }
    default:
      Supported = false;
      return;
    }
    for (unsigned I = 0; I != E.num_args(); ++I)
      Scan(E.arg(I));
  };
  Scan(Value);
  if (!Supported || Numerals.size() > 50000)
    return std::nullopt;
  std::set<CertInt> Points;
  for (const std::string &Numeral : Numerals)
    if (std::optional<CertInt> N = CertInt::fromDecimal(Numeral)) {
      Points.insert(*N);
      Points.insert(*N + CertInt(1));
    }
  auto read = [&](const CertInt &Address) -> std::optional<CertInt> {
    z3::expr Cell = Model.eval(
        z3::select(Value, Ctx.int_val(Address.toDecimal().c_str())), true);
    if (Decode)
      return Decode(Cell);
    std::string Numeral;
    if (!Cell.is_int() || !Cell.is_numeral(Numeral))
      return std::nullopt;
    return CertInt::fromDecimal(Numeral);
  };
  HeapValue Heap;
  const CertInt Below =
      Points.empty() ? CertInt(0) : *Points.begin() - CertInt(1);
  std::optional<CertInt> Default = read(Below);
  if (!Default)
    return std::nullopt;
  Heap.Default = *Default;
  for (const CertInt &Point : Points) {
    std::optional<CertInt> Cell = read(Point);
    if (!Cell)
      return std::nullopt;
    Heap.Breaks[Point] = *Cell;
  }
  Heap.normalize();
  return Heap;
}

std::optional<LogicValue> Z3Encoder::modelValue(const z3::model &Model,
                                                const z3::expr &Value,
                                                const LogicSort &Sort) {
  switch (Sort.Kind) {
  case LogicSortKind::Bool:
    if (Value.is_true() || Value.is_false())
      return LogicValue::boolean(Value.is_true());
    return std::nullopt;
  case LogicSortKind::Heap:
    if (std::optional<HeapValue> Heap = heapValue(Model, Value))
      return LogicValue::heap(std::move(*Heap));
    return std::nullopt;
  case LogicSortKind::Seq: {
    // seq.empty, seq.unit, and seq.++ of them.
    std::vector<CertInt> Elements;
    std::function<bool(const z3::expr &)> collect = [&](const z3::expr &E) {
      if (!E.is_app())
        return false;
      switch (E.decl().decl_kind()) {
      case Z3_OP_SEQ_EMPTY:
        return true;
      case Z3_OP_SEQ_UNIT: {
        std::string Numeral;
        if (!E.arg(0).is_numeral(Numeral))
          return false;
        std::optional<CertInt> Element = CertInt::fromDecimal(Numeral);
        if (!Element)
          return false;
        Elements.push_back(*Element);
        return true;
      }
      case Z3_OP_SEQ_CONCAT:
        for (unsigned I = 0; I != E.num_args(); ++I)
          if (!collect(E.arg(I)))
            return false;
        return true;
      default:
        return false;
      }
    };
    if (!collect(Model.eval(Value, true)))
      return std::nullopt;
    return LogicValue::sequence(std::move(Elements));
  }
  case LogicSortKind::Set: {
    auto Member = [](const z3::expr &Cell) -> std::optional<CertInt> {
      if (Cell.is_true() || Cell.is_false())
        return CertInt(Cell.is_true() ? 1 : 0);
      return std::nullopt;
    };
    if (std::optional<HeapValue> Members = piecewiseHeap(Model, Value, Member))
      return LogicValue::set(std::move(*Members));
    return std::nullopt;
  }
  case LogicSortKind::Multiset:
    if (std::optional<HeapValue> Counts = piecewiseHeap(Model, Value))
      return LogicValue::multiset(std::move(*Counts));
    return std::nullopt;
  case LogicSortKind::Map: {
    optionSort();
    auto Defined = [&](const z3::expr &Cell) -> std::optional<CertInt> {
      if (!Cell.is_app())
        return std::nullopt;
      if (Z3_is_eq_func_decl(Ctx, Cell.decl(), *NoneDecl))
        return CertInt(0);
      if (Z3_is_eq_func_decl(Ctx, Cell.decl(), *SomeDecl))
        return CertInt(1);
      return std::nullopt;
    };
    auto Stored = [&](const z3::expr &Cell) -> std::optional<CertInt> {
      if (!Cell.is_app())
        return std::nullopt;
      if (Z3_is_eq_func_decl(Ctx, Cell.decl(), *NoneDecl))
        return CertInt(0);
      std::string Numeral;
      if (!Z3_is_eq_func_decl(Ctx, Cell.decl(), *SomeDecl) ||
          !Cell.arg(0).is_numeral(Numeral))
        return std::nullopt;
      return CertInt::fromDecimal(Numeral);
    };
    std::optional<HeapValue> Domain = piecewiseHeap(Model, Value, Defined);
    std::optional<HeapValue> Values = piecewiseHeap(Model, Value, Stored);
    if (!Domain || !Values)
      return std::nullopt;
    return LogicValue::map(std::move(*Domain), std::move(*Values));
  }
  case LogicSortKind::MathematicalInteger:
  case LogicSortKind::Pointer:
  case LogicSortKind::BitVector: {
    std::string Numeral;
    if (!Value.is_numeral(Numeral))
      return std::nullopt;
    if (Value.is_bv()) {
      if (Sort.Kind != LogicSortKind::BitVector ||
          Value.get_sort().bv_size() != Sort.BitWidth)
        return std::nullopt;
      const unsigned Parsed = std::max<unsigned>(
          Sort.BitWidth, static_cast<unsigned>(Numeral.size()) * 4 + 2);
      return LogicValue::integer(CertInt::fromBits(
          llvm::APInt(Parsed, Numeral, 10).trunc(Sort.BitWidth),
          isSignedSort(Sort)));
    }
    if (!Value.is_int())
      return std::nullopt;
    if (std::optional<CertInt> Integer = CertInt::fromDecimal(Numeral))
      return LogicValue::integer(std::move(*Integer));
    return std::nullopt;
  }
  case LogicSortKind::Invalid:
    break;
  }
  return std::nullopt;
}

namespace clang {
namespace verify {
/// A Z3 model read through the encoder that produced its query.
class Z3CandidateModel : public CandidateModel {
  Z3Encoder &Encoder;
  z3::model Model;

public:
  Z3CandidateModel(Z3Encoder &Encoder, z3::model Model)
      : Encoder(Encoder), Model(std::move(Model)) {}

  std::optional<LogicValue> constant(const std::string &Name,
                                     const LogicSort &Sort) override {
    return Encoder.modelValue(
        Model, Model.eval(Encoder.symbol(Name, Sort), true), Sort);
  }

  std::optional<bool> validPointer(const CertInt &Address) override {
    z3::expr Valid = Model.eval(Encoder.validPointerDecl()(Encoder.Ctx.int_val(
                                    Address.toDecimal().c_str())),
                                true);
    if (Valid.is_true() || Valid.is_false())
      return Valid.is_true();
    return std::nullopt;
  }

  bool defined(const LogicFunctionDecl &Function) override {
    return Encoder.inlined(Function);
  }

  std::optional<LogicValue>
  application(const LogicFunctionDecl &Function,
              const std::vector<LogicValue> &Arguments) override {
    if (Arguments.size() != Function.Parameters.size() || defined(Function))
      return std::nullopt;
    const Table &Interpretation = table(Function);
    std::string Key;
    for (const LogicValue &Argument : Arguments)
      Key += "\x1f" + Argument.key();
    if (auto It = Interpretation.Entries.find(Key);
        It != Interpretation.Entries.end())
      return It->second;
    if (Interpretation.Else)
      return Interpretation.Else;
    z3::expr_vector Terms(Encoder.Ctx);
    for (unsigned I = 0; I != Arguments.size(); ++I)
      Terms.push_back(
          Encoder.valueTerm(Arguments[I], Function.Parameters[I].Sort));
    return read(Function,
                Model.eval(Encoder.specFuncDecl(Function)(Terms), true));
  }

private:
  /// A function's interpretation, indexed once per model.
  struct Table {
    std::map<std::string, LogicValue> Entries;
    std::optional<LogicValue> Else;
  };
  std::map<std::string, Table> Tables;

  /// The query reads an opaque machine-sorted application reduced in range.
  std::optional<LogicValue> read(const LogicFunctionDecl &Function,
                                 z3::expr Raw) {
    if (Encoder.integerMode() && Raw.is_numeral())
      Raw = Encoder.reduce(Raw, Function.ResultSort);
    return Encoder.modelValue(Model, Raw, Function.ResultSort);
  }

  const Table &table(const LogicFunctionDecl &Function) {
    auto [It, Inserted] = Tables.try_emplace(Function.Identity);
    if (!Inserted)
      return It->second;
    z3::func_decl Declaration = Encoder.specFuncDecl(Function);
    if (Function.Parameters.empty() || !Model.has_interp(Declaration))
      return It->second;
    z3::func_interp Interpretation = Model.get_func_interp(Declaration);
    for (unsigned I = 0; I != Interpretation.num_entries(); ++I) {
      z3::func_entry Entry = Interpretation.entry(I);
      if (Entry.num_args() != Function.Parameters.size())
        return It->second;
      std::string Key;
      for (unsigned A = 0; A != Entry.num_args(); ++A) {
        std::optional<LogicValue> Argument = Encoder.modelValue(
            Model, Entry.arg(A), Function.Parameters[A].Sort);
        if (!Argument)
          return It->second = Table();
        Key += "\x1f" + Argument->key();
      }
      std::optional<LogicValue> Value = read(Function, Entry.value());
      if (!Value)
        return It->second = Table();
      It->second.Entries.emplace(std::move(Key), std::move(*Value));
    }
    if (Z3_ast Else = Z3_func_interp_get_else(Encoder.Ctx, Interpretation);
        Else && z3::expr(Encoder.Ctx, Else).is_numeral())
      It->second.Else = read(Function, z3::expr(Encoder.Ctx, Else));
    return It->second;
  }
};
} // namespace verify
} // namespace clang

std::optional<z3::expr>
Z3Encoder::definitionInstance(const DefinitionInstance &Instance) {
  const LogicFunctionDecl &Function = *Instance.Function;
  if (!Function.StepDefinition ||
      Instance.Arguments.size() != Function.Parameters.size())
    return std::nullopt;
  z3::expr_vector Terms(Ctx);
  std::vector<std::pair<std::string, std::optional<z3::expr>>> Saved;
  for (unsigned I = 0; I != Instance.Arguments.size(); ++I) {
    const LogicFunctionParameter &Parameter = Function.Parameters[I];
    Terms.push_back(valueTerm(Instance.Arguments[I], Parameter.Sort));
    auto Existing = Vars.find(Parameter.Name);
    Saved.emplace_back(Parameter.Name,
                       Existing == Vars.end()
                           ? std::optional<z3::expr>()
                           : std::optional<z3::expr>(Existing->second));
    Vars.erase(Parameter.Name);
    Vars.emplace(Parameter.Name, Terms.back());
  }
  const bool SavedFailure = EncodingFailed;
  const bool SavedShadows = DefineBitShadows;
  EncodingFailed = false;
  DefineBitShadows = false;
  z3::expr Body = coerce(encodeVC(Function.StepDefinition.get()),
                         Function.StepDefinition->Sort, Function.ResultSort,
                         isSignedSort(Function.ResultSort));
  const bool Failed = EncodingFailed;
  EncodingFailed = SavedFailure;
  DefineBitShadows = SavedShadows;
  for (auto &[Name, Value] : Saved) {
    Vars.erase(Name);
    if (Value)
      Vars.emplace(Name, *Value);
  }
  if (Failed)
    return std::nullopt;
  return (specFuncDecl(Function)(Terms) == Body).simplify();
}

std::pair<z3::expr_vector, z3::expr>
Z3Encoder::encodeDefinition(const LogicFunctionDecl &Function) {
  z3::expr_vector Parameters(Ctx);
  std::vector<std::pair<std::string, std::optional<z3::expr>>> Saved;
  for (unsigned I = 0; I != Function.Parameters.size(); ++I) {
    const LogicFunctionParameter &Parameter = Function.Parameters[I];
    Parameters.push_back(Ctx.constant(
        ("def!" + Function.Identity + "!" + std::to_string(I)).c_str(),
        valueSort(Parameter.Sort)));
    auto Existing = Vars.find(Parameter.Name);
    Saved.emplace_back(Parameter.Name,
                       Existing == Vars.end()
                           ? std::optional<z3::expr>()
                           : std::optional<z3::expr>(Existing->second));
    Vars.erase(Parameter.Name);
    Vars.emplace(Parameter.Name, Parameters.back());
  }
  const bool SavedShadows = DefineBitShadows;
  DefineBitShadows = false;
  z3::expr Body = coerce(encodeVC(Function.StepDefinition.get()),
                         Function.StepDefinition->Sort, Function.ResultSort,
                         isSignedSort(Function.ResultSort));
  DefineBitShadows = SavedShadows;
  for (auto &[Name, Value] : Saved) {
    Vars.erase(Name);
    if (Value)
      Vars.emplace(Name, *Value);
  }
  return {Parameters, Body};
}

z3::expr Z3Encoder::inlineDefinition(const LogicFunctionDecl &Function,
                                     const std::vector<z3::expr> &Args) {
  auto It = Inlined.find(Function.Identity);
  if (It == Inlined.end()) {
    if (Function.DefinitionFuel == 0)
      NativeHidden.insert(Function.DisplayName.empty() ? Function.Identity
                                                       : Function.DisplayName);
    It = Inlined.emplace(Function.Identity, encodeDefinition(Function)).first;
  }
  z3::expr_vector Arguments(Ctx);
  for (const z3::expr &Arg : Args)
    Arguments.push_back(Arg);
  z3::expr Body = It->second.second;
  return Body.substitute(It->second.first, Arguments);
}

bool Z3Encoder::defineRecursiveFunctions() {
  while (!UndefinedRecursive.empty()) {
    const LogicFunctionDecl &Function = *UndefinedRecursive.back();
    UndefinedRecursive.pop_back();
    auto [Parameters, Body] = encodeDefinition(Function);
    if (EncodingFailed)
      return false;
    Ctx.recdef(SpecFuncDecls.at(Function.Identity), Parameters, Body);
  }
  return true;
}

namespace {
/// Resource budget for native recursive definitions without a timeout.
constexpr unsigned NativeRecursionResourceLimit = 25000000;
/// Least time refinement gets before native recursive definitions take over.
constexpr unsigned RefinementSliceMs = 500;
/// Least time the search among hidden definitions gets: with non-recursive
/// ones inlined it is an ordinary query, which must not miss a real
/// counterexample on a loaded machine.
constexpr unsigned HiddenSearchSliceMs = 2000;
constexpr unsigned HiddenRoundsBeforeNative = 8;
} // namespace

std::optional<VerifyResult> Z3Encoder::verifyNatively(
    const ObligationModule &Module, const LogicExpr *Query,
    std::optional<uint64_t> TraceEventCount, VerifyResult &FuelResult) {
  Z3Encoder Native;
  Native.NativeRecursion = true;
  Native.ProofOnly = ProofOnly;
  Native.setIntegerEncoding(IntegerEncoding);
  Native.setResourceLimit(ResourceLimit);
  if (TimeoutMs > 0) {
    const auto Remaining =
        std::chrono::duration_cast<std::chrono::milliseconds>(
            QueryStart + std::chrono::milliseconds(TimeoutMs) -
            std::chrono::steady_clock::now())
            .count();
    if (Remaining < 100)
      return std::nullopt;
    // After a hidden-spec stop the search can only find a counterexample, so
    // it gets a slice rather than the whole remaining budget.
    const bool SearchOnly = FuelResult.Reason == VerifyReason::SpecHidden;
    Native.setTimeoutMs(static_cast<unsigned>(
        SearchOnly
            ? std::min<long long>(Remaining,
                                  std::max(TimeoutMs / 50, HiddenSearchSliceMs))
            : Remaining));
  } else if (ResourceLimit == 0) {
    Native.setResourceLimit(FuelResult.Reason == VerifyReason::SpecHidden
                                ? NativeRecursionResourceLimit / 10
                                : NativeRecursionResourceLimit);
  }
  VerifyResult Result = Native.verifyModule(Module, Query, TraceEventCount);
  if (Result.Status == VerifyStatus::Verified ||
      Result.Status == VerifyStatus::Failed ||
      (Result.Reason == VerifyReason::SpecHidden &&
       FuelResult.Reason == VerifyReason::SpecHidden))
    return Result;
  FuelResult.Message += "; native recursive definitions did not settle it (" +
                        verifyReasonCode(Result.Reason).str() + ")";
  return std::nullopt;
}

std::vector<SpecDispute> Z3Encoder::boundedDomainDisputes(
    const ObligationModule &Module, const LogicExpr &Query,
    const CertifyResult &Disputed, const z3::model &Model,
    std::chrono::steady_clock::time_point Until, std::optional<z3::expr> &Pin) {
  constexpr unsigned MaxArguments = 4;
  constexpr unsigned MaxProbes = 96;
  std::set<std::string> Functions;
  for (const SpecDispute &Dispute : Disputed.Disputes)
    if (Dispute.Function->DefinitionFuel != 0)
      Functions.insert(Dispute.Function->Identity);

  // Integer arguments of their applications outside every binder.
  std::vector<z3::expr> Arguments;
  std::set<unsigned> Seen;
  const bool SavedFailure = EncodingFailed;
  const bool SavedShadows = DefineBitShadows;
  EncodingFailed = false;
  DefineBitShadows = false;
  std::vector<const LogicExpr *> Work{&Query};
  while (!Work.empty() && Arguments.size() < MaxArguments) {
    const LogicExpr *E = Work.back();
    Work.pop_back();
    if (!E || E->K == LogicExpr::Forall || E->K == LogicExpr::Exists)
      continue;
    for (const auto &Child : E->Children)
      Work.push_back(Child.get());
    if (E->K != LogicExpr::SpecCall || !Functions.count(E->SpecCallee))
      continue;
    for (const auto &Child : E->Children) {
      z3::expr Argument = encodeVC(Child.get());
      if (EncodingFailed)
        break;
      if (Argument.is_int() && !Argument.is_numeral() &&
          Seen.insert(Argument.id()).second && Arguments.size() < MaxArguments)
        Arguments.push_back(Argument);
    }
  }
  const bool Encoded = !EncodingFailed;
  EncodingFailed = SavedFailure;
  DefineBitShadows = SavedShadows;
  std::vector<SpecDispute> Found;
  if (!Encoded)
    return Found;

  auto check = [&]() {
    const auto Remaining =
        std::chrono::duration_cast<std::chrono::milliseconds>(
            Until - std::chrono::steady_clock::now())
            .count();
    if (Remaining <= 0)
      return z3::unknown;
    z3::params Params(Ctx);
    Params.set("timeout", static_cast<unsigned>(Remaining));
    Solver.set(Params);
    return this->check(Solver, static_cast<unsigned>(Remaining));
  };
  // The model at the extreme of \p Argument, if the solver proves one.
  auto extreme = [&](const z3::expr &Argument,
                     bool Greatest) -> std::optional<z3::model> {
    std::optional<z3::model> Best;
    z3::expr Current = Model.eval(Argument, true);
    if (!Current.is_numeral())
      return std::nullopt;
    int64_t Step = 1;
    for (unsigned Probe = 0; Probe != MaxProbes; ++Probe) {
      z3::expr Distance = Ctx.int_val(Step);
      Solver.push();
      Solver.add(Greatest ? Argument >= Current + Distance
                          : Argument <= Current - Distance);
      const z3::check_result Result = check();
      if (Result == z3::sat) {
        Best = Solver.get_model();
        Current = Best->eval(Argument, true);
        Solver.pop();
        if (!Current.is_numeral())
          return std::nullopt;
        if (Step < (int64_t(1) << 40))
          Step *= 2;
        continue;
      }
      Solver.pop();
      if (Result != z3::unsat)
        return std::nullopt;
      if (Step == 1)
        return Best;
      Step = 1;
    }
    return std::nullopt;
  };

  CertifyLimits Limits;
  if (TimeoutMs > 0)
    Limits.Deadline = QueryStart + std::chrono::milliseconds(TimeoutMs);
  for (const z3::expr &Argument : Arguments)
    for (bool Greatest : {true, false}) {
      std::optional<z3::model> Extreme = extreme(Argument, Greatest);
      if (!Extreme)
        continue;
      Z3CandidateModel Candidate(*this, *Extreme);
      CertifyResult Certified =
          certifyCounterexample(Module, Query, Candidate, Limits);
      if (Certified.Outcome == CertifyOutcome::Certified) {
        Pin = Argument == Extreme->eval(Argument, true);
        return {};
      }
      if (Certified.Outcome != CertifyOutcome::Disputed)
        continue;
      if (Found.size() + Certified.Disputes.size() >
          DefinitionRefinement::MaxInstances / 2)
        return {};
      Found.insert(Found.end(), Certified.Disputes.begin(),
                   Certified.Disputes.end());
    }
  return Found;
}

z3::check_result Z3Encoder::certifyModels(const ObligationModule &Module,
                                          const LogicExpr &Query,
                                          z3::check_result Result,
                                          VerifyResult &Out) {
  DefinitionRefinement Refinement(Module, NativeRecursion
                                              ? DefinitionRefinement::MaxRounds
                                              : HiddenRoundsBeforeNative);
  // Instances settle a few disputed points cheaply; beyond that the solver's
  // own unfolding of native recursive definitions does far better, so
  // refinement gets only a slice of the budget before they take over.
  std::optional<std::chrono::steady_clock::time_point> QueryDeadline;
  if (TimeoutMs > 0)
    QueryDeadline = QueryStart + std::chrono::milliseconds(TimeoutMs);
  std::optional<std::chrono::steady_clock::time_point> Deadline;
  if (NativeRecursion) {
    Deadline = QueryDeadline;
  } else {
    Deadline = std::chrono::steady_clock::now() +
               std::chrono::milliseconds(
                   TimeoutMs > 0 ? std::max(TimeoutMs / 20, RefinementSliceMs)
                                 : 4 * RefinementSliceMs);
  }
  EscalateToNative = false;
  auto stop = [&](const RefinementDecision &Decision) {
    Out.Status = VerifyStatus::Unresolved;
    Out.Reason = Decision.Reason;
    Out.Message = Decision.Message;
    EscalateToNative = !NativeRecursion && !Decision.Unbounded &&
                       !Decision.NoCounterexample &&
                       (Decision.Reason == VerifyReason::SpecFuel ||
                        Decision.Reason == VerifyReason::SpecHidden);
    return z3::unknown;
  };
  // Once a quantifier range is narrowed, the solver only searches among
  // small counterexamples: failing to find one settles nothing.
  unsigned Narrowed = 0;
  RefinementDecision Unchecked;
  bool OutOfTime = false;
  // Probing a domain happens once, and the check after it covered a bounded
  // domain is the proof attempt itself: it gets the whole remaining budget.
  bool Probed = false;
  bool Covered = false;
  auto check = [&]() {
    const auto Limit = Covered ? QueryDeadline : Deadline;
    Covered = false;
    if (!Limit)
      return this->check(Solver, 0);
    const auto Remaining =
        std::chrono::duration_cast<std::chrono::milliseconds>(
            *Limit - std::chrono::steady_clock::now())
            .count();
    if (Remaining <= 0) {
      OutOfTime = true;
      return z3::unknown;
    }
    z3::params Params(Ctx);
    Params.set("timeout", static_cast<unsigned>(Remaining));
    Solver.set(Params);
    return this->check(Solver, static_cast<unsigned>(Remaining));
  };
  while (Result == z3::sat) {
    z3::model Current = Solver.get_model();
    Z3CandidateModel Candidate(*this, Current);
    CertifyLimits Limits;
    Limits.Deadline = QueryDeadline;
    CertifyResult Certified =
        certifyCounterexample(Module, Query, Candidate, Limits);
    bool BoundedDomain = false;
    if (Certified.Outcome == CertifyOutcome::Disputed && !Probed &&
        !NativeRecursion && !Narrowed && !ProofOnly) {
      Probed = true;
      const auto Now = std::chrono::steady_clock::now();
      const auto Until = Deadline && *Deadline > Now
                             ? Now + (*Deadline - Now) / 2
                             : Now + std::chrono::milliseconds(250);
      std::optional<z3::expr> Pin;
      std::vector<SpecDispute> Extremes =
          boundedDomainDisputes(Module, Query, Certified, Current, Until, Pin);
      if (Pin) {
        // The pin only selects a counterexample: it stays only if the model
        // found under it is certified, so no unsat can ever rely on it.
        Solver.push();
        Solver.add(*Pin);
        if (check() == z3::sat) {
          Z3CandidateModel Pinned(*this, Solver.get_model());
          CertifyResult PinnedResult =
              certifyCounterexample(Module, Query, Pinned, Limits);
          if (PinnedResult.Outcome == CertifyOutcome::Certified) {
            Out.CertifiedWith = std::move(PinnedResult.Evidence);
            return z3::sat;
          }
        }
        Solver.pop();
      } else if (!Extremes.empty()) {
        if (!integerMode()) {
          CoverInIntegers = true;
          return z3::unknown;
        }
        Certified.Disputes.insert(Certified.Disputes.end(), Extremes.begin(),
                                  Extremes.end());
        BoundedDomain = true;
      }
    }
    if (Certified.Outcome == CertifyOutcome::Undetermined &&
        Certified.DefinitionTooDeep && Certified.DeepApplication &&
        Narrowed < MaxNarrowedQuantifiers) {
      if (Narrowed++ == 0)
        Unchecked = Refinement.next(Certified);
      const bool SavedFailure = EncodingFailed;
      const bool SavedShadows = DefineBitShadows;
      EncodingFailed = false;
      DefineBitShadows = false;
      z3::expr_vector Bounds(Ctx);
      for (const auto &Argument : Certified.DeepApplication->Children) {
        z3::expr Value = encodeVC(Argument.get());
        if (EncodingFailed)
          break;
        const int Bound = static_cast<int>(NarrowedArgumentBound);
        if (Value.is_int()) {
          Bounds.push_back(Value <= Ctx.int_val(Bound) &&
                           Value >= Ctx.int_val(-Bound));
        } else if (Value.is_bv() && Value.get_sort().bv_size() > 13) {
          const unsigned Width = Value.get_sort().bv_size();
          if (Argument->Sort.Signedness == LogicSignedness::Signed)
            Bounds.push_back(z3::sle(Value, Ctx.bv_val(Bound, Width)) &&
                             z3::sge(Value, Ctx.bv_val(-Bound, Width)));
          else
            Bounds.push_back(z3::ule(Value, Ctx.bv_val(Bound, Width)));
        }
      }
      const bool Encoded = !EncodingFailed && !Bounds.empty();
      EncodingFailed = SavedFailure;
      DefineBitShadows = SavedShadows;
      if (!Encoded)
        return stop(Unchecked);
      Solver.add(z3::mk_and(Bounds));
      Result = check();
      if (Result != z3::sat)
        return stop(Unchecked);
      continue;
    }
    if (Certified.Outcome == CertifyOutcome::Undetermined &&
        Certified.WideQuantifier && Narrowed < MaxNarrowedQuantifiers) {
      if (Narrowed++ == 0)
        Unchecked = Refinement.next(Certified);
      const bool SavedFailure = EncodingFailed;
      const bool SavedShadows = DefineBitShadows;
      EncodingFailed = false;
      DefineBitShadows = false;
      z3::expr Low = encodeVC(Certified.WideQuantifier->Children[0].get());
      z3::expr High = encodeVC(Certified.WideQuantifier->Children[1].get());
      const bool Encoded = !EncodingFailed && Low.is_int() && High.is_int();
      EncodingFailed = SavedFailure;
      DefineBitShadows = SavedShadows;
      if (!Encoded)
        return stop(Unchecked);
      Solver.add(High - Low <=
                 Ctx.int_val(static_cast<int>(NarrowedQuantifierRange)));
      Result = check();
      if (Result != z3::sat)
        return stop(Unchecked);
      continue;
    }
    RefinementDecision Decision = Refinement.next(Certified, BoundedDomain);
    Covered =
        BoundedDomain && Decision.Next == RefinementDecision::Action::Refine;
    if (Decision.Next == RefinementDecision::Action::Report) {
      Out.CertifiedWith = Certified.Evidence;
      return Result;
    }
    if (Decision.Next == RefinementDecision::Action::Stop)
      return stop(Narrowed && Decision.Reason == VerifyReason::SpecFuel
                      ? Unchecked
                      : Decision);
    for (const DefinitionInstance &Instance : Decision.Instances) {
      std::optional<z3::expr> Equation = definitionInstance(Instance);
      if (!Equation) {
        RefinementDecision Failed;
        Failed.Reason = VerifyReason::EncodingFailure;
        Failed.Message = "cannot encode a definition instance of " +
                         Instance.Function->DisplayName;
        return stop(Failed);
      }
      Solver.add(*Equation);
    }
    if (Covered) {
      // Thousands of ground equations are solved far faster from scratch
      // than by the incremental core this solver has switched to.
      z3::solver Fresh = freshSolver();
      Fresh.add(Solver.assertions());
      Solver = Fresh;
    }
    Result = check();
    if (Narrowed && Result != z3::sat)
      return stop(Unchecked);
    if (Result == z3::unknown)
      return stop(OutOfTime
                      ? Refinement.exhausted()
                      : Refinement.exhausted("then z3 returned unknown: " +
                                             Solver.reason_unknown()));
    if (Result == z3::unsat)
      if (std::optional<RefinementDecision> Hidden = Refinement.unsatisfiable())
        return stop(*Hidden);
  }
  return Result;
}

VerifyResult Z3Encoder::verifyModule(const ObligationModule &Module,
                                     const LogicExpr *Query,
                                     std::optional<uint64_t> TraceEventCount) {
  VerifyResult Out;
  QueryStart = std::chrono::steady_clock::now();
  const bool IsCompleteQuery = Query == nullptr;
  auto EncodedGoal = encodeModule(Module, Query, Out);
  if (!EncodedGoal)
    return Out;
  Solver.add(*EncodedGoal);
  for (const z3::expr &Definition : BitDefinitions)
    Solver.add(Definition);
  const LogicExpr &Asked = Query ? *Query : *Module.CounterexampleQuery;
  if (!NativeRecursion) {
    // Applications at closed arguments are computed, not searched for.
    CertifyLimits Limits;
    if (TimeoutMs > 0)
      Limits.Deadline = QueryStart + std::chrono::milliseconds(TimeoutMs);
    for (const DefinitionInstance &Instance :
         closedApplicationInstances(Module, Asked, Limits))
      if (std::optional<z3::expr> Equation = definitionInstance(Instance))
        Solver.add(*Equation);
  }
  z3::expr Semantics = z3::mk_and(Solver.assertions());
  for (const z3::expr &Axiom : CollectionAxioms)
    Solver.add(Axiom);
  Solver.add(rangeFacts());
  const z3::expr_vector Asserted = Solver.assertions();
  const z3::check_result Checked =
      certifyModels(Module, Asked, check(Solver, TimeoutMs), Out);
  if (ProfileQuantifiers && Checked == z3::unknown && QuantifiedQuery)
    Out.QuantifierProfile = profileQuantifiers(Asserted);
  if (CoverInIntegers) {
    Z3Encoder Integers;
    Integers.setIntegerEncoding(MachineIntegerEncoding::Integer);
    Integers.setResourceLimit(ResourceLimit);
    Integers.setProofOnly(ProofOnly);
    if (TimeoutMs > 0) {
      const auto Remaining =
          std::chrono::duration_cast<std::chrono::milliseconds>(
              QueryStart + std::chrono::milliseconds(TimeoutMs) -
              std::chrono::steady_clock::now())
              .count();
      Integers.setTimeoutMs(
          static_cast<unsigned>(std::max<long long>(Remaining, 1)));
    }
    return Integers.verifyModule(Module, Query, TraceEventCount);
  }
  if (Out.Reason != VerifyReason::None) {
    if (EscalateToNative)
      if (std::optional<VerifyResult> Native =
              verifyNatively(Module, Query, TraceEventCount, Out))
        return std::move(*Native);
    return Out;
  }
  switch (Checked) {
  case z3::unsat:
    if (!NativeHidden.empty()) {
      std::string Names;
      for (const std::string &Name : NativeHidden)
        Names += (Names.empty() ? "" : ", ") + Name;
      Out.Status = VerifyStatus::Unresolved;
      Out.Reason = VerifyReason::SpecHidden;
      Out.Message = "no counterexample exists, but the proof needs the "
                    "definition of " +
                    Names +
                    ", which is hidden from the solver; reveal it or state a "
                    "lemma";
      return Out;
    }
    Out.Status = VerifyStatus::Verified;
    return Out;
  case z3::sat: {
    Out.Status = VerifyStatus::Failed;
    Out.Reason = VerifyReason::Counterexample;
    z3::model Mod = Solver.get_model();
    // Range facts assign every machine variable; report those the goal does
    // not depend on as unknown. Divisor variables stay assigned (slow eval),
    // as does everything under native recursive definitions, which the model
    // evaluator would unfold without bound at an unassigned argument.
    z3::expr_vector Assigned(Ctx), Unassigned(Ctx);
    std::set<std::string> Freed;
    if (integerMode() && !NativeRecursion) {
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
    // A diagnostic term dividing by a freed variable is undetermined. With
    // native recursive definitions every term is read in the completed model,
    // the one the certifier checked.
    auto modelValue = [&](z3::expr Encoded) {
      if (NativeRecursion)
        return Mod.eval(Encoded, true);
      if (Freed.empty())
        return Mod.eval(Encoded, false);
      z3::expr Substituted = Encoded.substitute(Assigned, Unassigned);
      for (const std::string &Name : divisorConstants(Encoded))
        if (Freed.count(Name))
          return Substituted;
      return Mod.eval(Substituted, false);
    };
    auto sourceValue = [&](const z3::expr &Evaluated,
                           const LogicSort &Sort) -> std::optional<std::string> {
      if (!Sort.isCollection())
        return sourceModelValue(Evaluated, Sort);
      if (std::optional<LogicValue> Value =
              Z3Encoder::modelValue(Mod, Evaluated, Sort))
        return formatLogicValue(*Value);
      return std::nullopt;
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
      return sourceValue(Evaluated, Expr->Sort);
    };
    if (IsCompleteQuery && !TraceEventCount) {
      // The certified model is the completed one; the certifier evaluates
      // what the solver's evaluator leaves open, such as quantifiers.
      Z3CandidateModel Candidate(*this, Mod);
      CertifyLimits Limits;
      Limits.Deadline = std::chrono::steady_clock::now() +
                        std::chrono::milliseconds(
                            std::max(TimeoutMs / 10, RefinementSliceMs));
      auto fails = [&](const Obligation &Item) {
        std::optional<std::string> Fails =
            evaluate(Item.CounterexampleQuery.get());
        if (Fails)
          return *Fails == "true";
        std::optional<LogicValue> Value = evaluateTerm(
            Module, *Item.CounterexampleQuery, Candidate, Limits);
        return Value && Value->K == LogicValue::Kind::Bool && Value->Truth;
      };
      for (const Obligation &Item : Module.Obligations) {
        if (!fails(Item))
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
          Value.Value = sourceValue(Evaluated, Sort);
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
    if (TimeoutMs > 0 && (Reason.equals_insensitive("timeout") || Overran)) {
      Out.Reason = VerifyReason::SolverTimeout;
      Out.Message = "timeout";
    } else if (ResourceLimit > 0 &&
               Reason.contains_insensitive("resource limit"))
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
    for (const std::string &Name : UsedCellDecls)
      *OS << CellDecls.at(Name).second << "\n";
    if (!CollectionAxioms.empty())
      *OS << "(define-fun-rec cppverify.seq_at ((s (Seq Int)) (i Int)) Int "
             "(ite (and (<= 0 i) (< i (seq.len s))) (seq.nth s i) 0))\n";
    for (const z3::expr &Axiom : CollectionAxioms)
      *OS << Axiom.to_string() << "\n";
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

static VerifyResult timeSpent() {
  VerifyResult Result;
  Result.BackendName = "z3";
  Result.Status = VerifyStatus::Unresolved;
  Result.Reason = VerifyReason::SolverTimeout;
  Result.Message = "the function's time (--function-timeout) is spent";
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
                                   bool StopAtFailure, Race *Racing) {
  TimeoutMs =
      budget(moduleTimeoutMs(Module, SolverTimeoutMs, CollectionTimeoutMs));
  Enc.setTimeoutMs(TimeoutMs);
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
          Cache ? &CacheLookups[I] : nullptr, IsReused(I), Racing));
      if (StopAtFailure && Results.back().Status == VerifyStatus::Failed)
        break;
    }
  } else {
    // On the driver's pool when there is one: waiting on the group from a
    // worker runs its tasks, so nesting cannot exceed the jobs.
    std::optional<llvm::StdThreadPool> OwnPool;
    if (!Pool)
      OwnPool.emplace(llvm::heavyweight_hardware_concurrency(Jobs));
    llvm::ThreadPoolTaskGroup Group(Pool ? *Pool : *OwnPool);
    std::vector<std::shared_future<VerifyResult>> Futures;
    Futures.reserve(Module.Obligations.size());
    for (size_t I = 0; I != Module.Obligations.size(); ++I) {
      Futures.push_back(Group.async(
          [this, &Module, &CacheHashes, &CacheLookups, &IsReused, I, Racing] {
            return verifyObligation(
                Module, Module.Obligations[I],
                Cache ? llvm::StringRef(CacheHashes[I]) : llvm::StringRef(),
                Cache ? &CacheLookups[I] : nullptr, IsReused(I), Racing);
          }));
    }
    Group.wait();
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
      SolverTimeoutMs(Execution.SolverTimeoutMs),
      CollectionTimeoutMs(Execution.CollectionTimeoutMs),
      ResourceLimit(Execution.SolverResourceLimit), Jobs(Execution.Jobs),
      Pool(Execution.Pool), MaxQueryNodes(Execution.MaxQueryNodes),
      IntegerEncoding(Execution.IntegerEncoding),
      SkipWholeModuleRetry(Execution.SkipWholeModuleRetry),
      SingleQuery(Execution.SingleQuery),
      ProfileQuantifiers(Execution.ProfileQuantifiers),
      ReuseVerifiedQueries(ReuseVerifiedQueries) {
  Enc.setTimeoutMs(TimeoutMs);
  Enc.setResourceLimit(ResourceLimit);
  Enc.setIntegerEncoding(IntegerEncoding);
  Enc.setProfileQuantifiers(ProfileQuantifiers);
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

void Z3VerifyBackend::Race::enter(Z3Encoder &Encoder) {
  std::lock_guard<std::mutex> Guard(Lock);
  Running.insert(&Encoder);
  if (Cancelled)
    Encoder.interrupt();
}

void Z3VerifyBackend::Race::leave(Z3Encoder &Encoder) {
  std::lock_guard<std::mutex> Guard(Lock);
  Running.erase(&Encoder);
}

void Z3VerifyBackend::Race::cancel() {
  std::lock_guard<std::mutex> Guard(Lock);
  Cancelled = true;
  for (Z3Encoder *Encoder : Running)
    Encoder->interrupt();
}

bool Z3VerifyBackend::racesEncodings(const ObligationModule &Module) const {
  return Jobs != 1 &&
         (Module.RequiredFeatures & logicFeature(LogicFeature::Sequences));
}

VerifyResult Z3VerifyBackend::solveQuery(
    const ObligationModule &Module, const LogicExpr *Query,
    std::optional<uint64_t> TraceEventCount, unsigned Timeout, Race *Racing) {
  auto solve = [&](bool Facts, Race *Pair) {
    Z3Encoder Encoder;
    Encoder.setTimeoutMs(Timeout);
    Encoder.setResourceLimit(ResourceLimit);
    Encoder.setIntegerEncoding(IntegerEncoding);
    Encoder.setProfileQuantifiers(ProfileQuantifiers && Facts);
    Encoder.setSequenceFacts(Facts);
    if (Racing)
      Racing->enter(Encoder);
    if (Pair)
      Pair->enter(Encoder);
    VerifyResult Result = Encoder.verifyModule(Module, Query, TraceEventCount);
    if (Pair)
      Pair->leave(Encoder);
    if (Racing)
      Racing->leave(Encoder);
    return Result;
  };
  if (!racesEncodings(Module))
    return solve(true, nullptr);
  // Sequence facts are theorems that help proofs but slow model search (a
  // false claim over a chain of 200 pushes took minutes with them and 0.1 s
  // without), so with workers to spare the query is also solved without
  // them. Both are exact: the first proof or certified counterexample
  // stands and stops the other.
  auto decisive = [](const VerifyResult &Result) {
    return Result.Status == VerifyStatus::Verified ||
           Result.Status == VerifyStatus::Failed;
  };
  Race Pair;
  std::optional<llvm::StdThreadPool> OwnPool;
  if (!Pool)
    OwnPool.emplace(llvm::heavyweight_hardware_concurrency(2));
  llvm::ThreadPoolTaskGroup Group(Pool ? *Pool : *OwnPool);
  VerifyResult Plain;
  Group.async([&] {
    Plain = solve(false, &Pair);
    if (decisive(Plain))
      Pair.cancel();
  });
  VerifyResult WithFacts = solve(true, &Pair);
  if (decisive(WithFacts))
    Pair.cancel();
  Group.wait();
  if (!decisive(WithFacts) && decisive(Plain))
    return Plain;
  return WithFacts;
}

VerifyResult Z3VerifyBackend::verifyObligation(const ObligationModule &Module,
                                               const Obligation &Item,
                                               llvm::StringRef SemanticHash,
                                               const ProofCacheLookup *Lookup,
                                               bool Reused, Race *Racing) {
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
    Result = spent()
                 ? timeSpent()
                 : solveQuery(Module, Item.CounterexampleQuery.get(),
                              Item.TraceEventCount, budget(TimeoutMs), Racing);
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

std::optional<VerifyResult>
Z3VerifyBackend::proveByInduction(const ObligationModule &Module,
                                  const Obligation *Item,
                                  std::vector<std::string> *Tried) {
  // No finite unfolding settles the goal: try strong induction on a variable
  // that the refuted applications grow with.
  constexpr unsigned MaxInductionVariables = 2;
  unsigned Attempts = 0;
  for (const auto &[Variable, Sort] : inductionVariables(Module, Item)) {
    if (Attempts++ == MaxInductionVariables || spent())
      break;
    auto Inductive = inductionModule(Module, Variable, Sort, Item);
    if (!Inductive) {
      llvm::consumeError(Inductive.takeError());
      continue;
    }
    if (Tried)
      Tried->push_back(Variable);
    // Both encodings are exact; bit-vector conversions of the binder would
    // hide the hypothesis from instantiation.
    Z3Encoder Encoder;
    Encoder.setTimeoutMs(budget(inductionBudgetMs(TimeoutMs)));
    Encoder.setResourceLimit(ResourceLimit);
    Encoder.setIntegerEncoding(IntegerEncoding ==
                                       MachineIntegerEncoding::BitVector
                                   ? MachineIntegerEncoding::Auto
                                   : IntegerEncoding);
    Encoder.setProofOnly(true);
    VerifyResult Proof = Encoder.verifyModule(*Inductive);
    if (Proof.Status == VerifyStatus::Verified)
      return Proof;
  }
  return std::nullopt;
}

VerifyResult Z3VerifyBackend::verifyModule(const ObligationModule &Module) {
  TimeoutMs =
      budget(moduleTimeoutMs(Module, SolverTimeoutMs, CollectionTimeoutMs));
  Enc.setTimeoutMs(TimeoutMs);
  if (SingleQuery) {
    if (auto Limit = querySizeLimitResult(Module, MaxQueryNodes))
      return std::move(*Limit);
    if (spent())
      return timeSpent();
    return finishZ3Result(Enc.verifyModule(Module));
  }
  VerifyResult Result = verifyModuleDirect(Module);
  // The integer encoding is as exact: where bit-blasting gives up, it often
  // settles the same query.
  if (IntegerEncoding == MachineIntegerEncoding::BitVector && !spent() &&
      Result.Status == VerifyStatus::Unresolved &&
      (Result.Reason == VerifyReason::SolverTimeout ||
       Result.Reason == VerifyReason::SolverUnknown ||
       Result.Reason == VerifyReason::SolverResourceLimit)) {
    IntegerEncoding = MachineIntegerEncoding::Auto;
    Enc.setIntegerEncoding(IntegerEncoding);
    VerifyResult Retry = verifyModuleDirect(Module);
    IntegerEncoding = MachineIntegerEncoding::BitVector;
    Enc.setIntegerEncoding(IntegerEncoding);
    if (Retry.Status != VerifyStatus::Unresolved ||
        Retry.Reason == VerifyReason::SpecFuel)
      Result = std::move(Retry);
  }
  if (Result.Status != VerifyStatus::Unresolved ||
      Result.Reason != VerifyReason::SpecFuel)
    return Result;
  std::vector<std::string> Tried;
  std::optional<VerifyResult> Proof = proveByInduction(Module, nullptr, &Tried);
  if (!Proof) {
    Result.Message += inductionNote(Module, Tried);
    return Result;
  }
  Proof->CacheHits = Result.CacheHits;
  Proof->CacheMisses = Result.CacheMisses;
  Proof->CacheErrors = Result.CacheErrors;
  Proof->CacheError = Result.CacheError;
  Proof->ReusedQueries = Result.ReusedQueries;
  return std::move(*Proof);
}

VerifyResult
Z3VerifyBackend::verifyModuleDirect(const ObligationModule &Module) {
  if (auto Limit = querySizeLimitResult(Module, MaxQueryNodes))
    return std::move(*Limit);
  if (spent())
    return timeSpent();
  // The cache holds proofs of single obligations.
  if (Cache) {
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
      if (!CacheFailure && !SkipWholeModuleRetry && !spent()) {
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

  // Spec equations often solve best as one formula, so with specs the
  // complete VC gets the full budget. Over collections, one hard obligation
  // can make it far harder than every ordered one (a ghost-sequence sum loop
  // timed out whole after 30 s; its obligations take 0.2 s), so there it gets
  // a sixth (at least 5 s) before them and the rest after. For spec-free
  // programs, a short probe preserves the budget for the ordered obligations.
  const bool OverCollections =
      Module.RequiredFeatures & (logicFeature(LogicFeature::Sequences) |
                                 logicFeature(LogicFeature::Collections));
  const unsigned WholeBudget =
      Module.LogicFunctions.empty()
          ? 500U
          : (TimeoutMs == 0 || !OverCollections
                 ? TimeoutMs
                 : std::max(TimeoutMs / 6, 5000U));
  const bool WholeUsedFullBudget =
      TimeoutMs == 0 ? !Module.LogicFunctions.empty()
                     : WholeBudget >= TimeoutMs;
  // With workers to spare, the obligations are solved one by one beside the
  // whole query. Both are exact, so whichever settles the module first
  // decides it and interrupts the other. The whole query then runs in an
  // encoder of its own, since an interrupt can outlive the check it stops.
  const bool Racing = Jobs != 1 && Module.Obligations.size() > 1;
  const unsigned WholeTimeout =
      budget(WholeUsedFullBudget ? TimeoutMs : WholeBudget);
  Race Rivals;
  Race WholeRace;
  std::optional<llvm::StdThreadPool> OwnPool;
  std::optional<llvm::ThreadPoolTaskGroup> Group;
  std::shared_future<std::vector<VerifyResult>> Ordered;
  if (Racing) {
    // Without the driver's pool, one of its own serves both strategies.
    if (!Pool) {
      OwnPool.emplace(llvm::heavyweight_hardware_concurrency(Jobs));
      Pool = &*OwnPool;
    }
    Group.emplace(*Pool);
    Ordered = Group->async([this, &Module, &Rivals, &WholeRace] {
      std::vector<VerifyResult> Results =
          verifyObligations(Module, /*StopAtFailure=*/true, &Rivals);
      if (Results.size() == Module.Obligations.size() &&
          llvm::all_of(Results, [](const VerifyResult &R) {
            return R.Status == VerifyStatus::Verified;
          }))
        WholeRace.cancel();
      return Results;
    });
  }
  VerifyResult Whole;
  if (Racing) {
    Whole = solveQuery(Module, nullptr, std::nullopt, WholeTimeout, &WholeRace);
    if (Whole.Status == VerifyStatus::Verified)
      Rivals.cancel();
    Group->wait();
    if (OwnPool)
      Pool = nullptr;
  } else if (racesEncodings(Module)) {
    Whole = solveQuery(Module, nullptr, std::nullopt, WholeTimeout, nullptr);
  } else {
    Enc.setTimeoutMs(WholeTimeout);
    Whole = Enc.verifyModule(Module);
  }
  Enc.setTimeoutMs(budget(TimeoutMs));
  if (Whole.Status == VerifyStatus::Verified)
    return finishZ3Result(std::move(Whole));
  auto orderedResults = [&] {
    return Racing ? Ordered.get()
                  : verifyObligations(Module, /*StopAtFailure=*/true);
  };

  if (Whole.Status == VerifyStatus::Failed) {
    bool SawUnresolved = false;
    for (VerifyResult Result : orderedResults()) {
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
    if (WholeUsedFullBudget || SkipWholeModuleRetry || spent())
      return finishZ3Result(std::move(SplitResult));
    VerifyResult Retry;
    if (racesEncodings(Module)) {
      Retry =
          solveQuery(Module, nullptr, std::nullopt, budget(TimeoutMs), nullptr);
    } else {
      Enc.setTimeoutMs(budget(TimeoutMs));
      Retry = Enc.verifyModule(Module);
    }
    if (Retry.Status != VerifyStatus::Unresolved)
      return finishZ3Result(std::move(Retry));
    return finishZ3Result(std::move(SplitResult));
  };

  std::vector<VerifyResult> Results = orderedResults();
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