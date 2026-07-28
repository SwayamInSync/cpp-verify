//===--- Z3Encode.cpp -----------------------------------------------------===//
#include "Z3Encode.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>
#include <cassert>

using namespace clang;
using namespace verify;

namespace {

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

void collectSpecCalls(const VCExpr *Expression,
                      std::vector<const VCExpr *> &Calls) {
  if (!Expression)
    return;
  if (Expression->K == VCExpr::SpecCall)
    Calls.push_back(Expression);
  for (const auto &Child : Expression->Children)
    collectSpecCalls(Child.get(), Calls);
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
    return bvSort(Sort.BitWidth);
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
    return Ctx.bv_val(0, E->Sort.BitWidth);
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
      return Ctx.bv_val(E->IntVal.c_str(), E->Sort.BitWidth);
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
      Z = Ctx.bv_const(E->Name.c_str(), E->Sort.BitWidth);
    } else {
      markEncodingFailure("unsupported variable sort: " + E->Name);
      Z = Ctx.int_const(E->Name.c_str());
    }
    Vars.emplace(E->Name, Z);
    return Z;
  }
  case VCExpr::IntToBv: {
    z3::expr Inner = child(0);
    if (Inner.is_int())
      return z3::int2bv(E->Sort.BitWidth, Inner);
    if (Inner.is_bv())
      return Inner;
    markEncodingFailure("cannot convert non-integer expression to bit-vector");
    return fallbackValue(E);
  }
  case VCExpr::BvResize: {
    z3::expr Inner = child(0);
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
    z3::expr T = coerceToSort(child(1), E->Sort, IsSigned);
    z3::expr F = coerceToSort(child(2), E->Sort, IsSigned);
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
    return arithOp(E, child(0), child(1));
  }
  case VCExpr::Neg:
    return -child(0);
  case VCExpr::BitNot: {
    z3::expr Value = child(0);
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
    return coerceToSort(Val, E->Sort,
                        E->Sort.Signedness == LogicSignedness::Signed);
  }
  case VCExpr::Store: {
    z3::expr Before = child(0);
    z3::expr Ptr = heapIndex(child(1));
    z3::expr Val = heapCellValue(child(2));
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
      z3::expr Arg = coerceToSort(child(i), Function.Parameters[i].Sort,
                                  Function.Parameters[i].Sort.Signedness ==
                                      LogicSignedness::Signed);
      Args.push_back(std::move(Arg));
    }
    z3::expr A = F(static_cast<unsigned>(Args.size()), Args.data());
    return coerceToSort(
        A, E->Sort, Function.ResultSort.Signedness == LogicSignedness::Signed);
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
    Arg = coerceToSort(Arg, Function.Parameters[I].Sort,
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
    RHS =
        coerceToSort(RHS, Function.ResultSort,
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
  if (!Query)
    Query = Module.CounterexampleQuery.get();
  Vars.clear();
  Solver = containsQuantifier(Query) ? z3::tactic(Ctx, "smt").mk_solver()
                                     : z3::solver(Ctx);
  z3::params Params(Ctx);
  if (TimeoutMs > 0)
    Params.set("timeout", TimeoutMs);
  Params.set("mbqi", true);
  Params.set("qi.eager_threshold", 0.0);
  Solver.set(Params);
  EncodingFailed = false;
  EncodingError.clear();
  LogicFunctions.clear();
  SpecFuncDecls.clear();
  for (const auto &[Identity, Function] : Module.LogicFunctions)
    LogicFunctions.emplace(Identity, &Function);
  if (!Query) {
    Result.Status = VerifyStatus::Unresolved;
    Result.Message = "missing counterexample query";
    return std::nullopt;
  }
  std::vector<const VCExpr *> SpecCalls;
  collectSpecCalls(Query, SpecCalls);
  for (const VCExpr *Call : SpecCalls)
    emitSpecCallAxiom(Call);
  Vars.clear();
  z3::expr EncodedGoal = encodeVC(Query);
  if (EncodingFailed) {
    Result.Status = VerifyStatus::Unresolved;
    Result.Message = EncodingError;
    return std::nullopt;
  }
  return EncodedGoal;
}

VerifyResult Z3Encoder::verifyModule(const ObligationModule &Module,
                                     const LogicExpr *Query) {
  VerifyResult Out;
  auto EncodedGoal = encodeModule(Module, Query, Out);
  if (!EncodedGoal)
    return Out;
  Solver.add(*EncodedGoal);
  switch (Solver.check()) {
  case z3::unsat:
    Out.Status = VerifyStatus::Verified;
    return Out;
  case z3::sat: {
    Out.Status = VerifyStatus::Failed;
    z3::model Mod = Solver.get_model();
    for (const auto &KV : Vars) {
      z3::expr Val = Mod.eval(KV.second, true);
      Out.Model[KV.first] = Val.to_string();
    }
    return Out;
  }
  default:
    Out.Status = VerifyStatus::Unresolved;
    Out.Message = Solver.reason_unknown();
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
  if (OS)
    *OS << EncodedGoal->to_string() << "\n";
  Out.Status = VerifyStatus::Lowered;
  return Out;
}

static VerifyResult finishZ3Result(VerifyResult Result) {
  if (Result.Status != VerifyStatus::Failed)
    return Result;
  std::string Message;
  for (const auto &KV : Result.Model) {
    if (!Message.empty())
      Message += ", ";
    Message += KV.first + " = " + KV.second;
  }
  Result.Message = std::move(Message);
  return Result;
}

std::vector<VerifyResult>
Z3VerifyBackend::verifyObligations(const ObligationModule &Module) {
  Enc.setTimeoutMs(TimeoutMs);
  std::vector<VerifyResult> Results;
  Results.reserve(Module.Obligations.size());
  for (const Obligation &Item : Module.Obligations) {
    VerifyResult Result =
        Enc.verifyModule(Module, Item.CounterexampleQuery.get());
    Result.ObligationId = Item.Id;
    Result.ObligationType = Item.Kind;
    Result.Location = Item.Loc;
    if (Result.Status == VerifyStatus::Unresolved)
      Result.Message = "proof obligation " + Item.Id +
                       (Result.Message.empty() ? "" : ": " + Result.Message);
    Results.push_back(finishZ3Result(std::move(Result)));
  }
  return Results;
}

VerifyResult Z3VerifyBackend::verifyModule(const ObligationModule &Module) {

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
    for (VerifyResult Result : verifyObligations(Module)) {
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
    Inconsistent.Message =
        "combined query was satisfiable but every individual obligation was "
        "proved";
    return Inconsistent;
  }

  auto retryWhole = [&](VerifyResult SplitResult) {
    if (WholeUsedFullBudget)
      return finishZ3Result(std::move(SplitResult));
    VerifyResult Retry = Enc.verifyModule(Module);
    if (Retry.Status != VerifyStatus::Unresolved)
      return finishZ3Result(std::move(Retry));
    return finishZ3Result(std::move(SplitResult));
  };

  std::optional<VerifyResult> FirstUnresolved;
  for (VerifyResult Result : verifyObligations(Module)) {
    if (Result.Status != VerifyStatus::Verified) {
      if (Result.Status == VerifyStatus::Unresolved) {
        if (!FirstUnresolved)
          FirstUnresolved = std::move(Result);
        continue;
      }
      return Result;
    }
  }

  if (FirstUnresolved)
    return retryWhole(std::move(*FirstUnresolved));

  VerifyResult R;
  R.Status = VerifyStatus::Verified;
  return R;
}