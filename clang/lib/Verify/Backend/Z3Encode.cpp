//===--- Z3Encode.cpp -----------------------------------------------------===//
#include "Z3Encode.h"
#include "SpecAxioms.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

using namespace clang;
using namespace verify;

Z3Encoder::Z3Encoder() : Ctx(), Solver(Ctx) {}

z3::sort Z3Encoder::intSort() { return Ctx.int_sort(); }
z3::sort Z3Encoder::bvSort() { return Ctx.bv_sort(32); }
z3::sort Z3Encoder::boolSort() { return Ctx.bool_sort(); }
// Heap is Array Int BitVec32: integer pointer addresses (exact, so distinct
// pointers never alias mod 2^32) mapping to machine-integer cell values. Storing
// values as bit-vectors avoids int2bv/bv2int round-trips on every load/store,
// which put queries in the arrays+int<->bv fragment Z3 fails to decide.
// Heap indices are mathematical-integer addresses (pointers are encoded as Int);
// values are 32-bit machine words. Integer addresses make pointer arithmetic and
// the buffer non-overlap condition wrap-free linear arithmetic, and `p + i` is
// the index directly — no bv<->int round-trip, since the address is already Int.
z3::sort Z3Encoder::heapSort() { return Ctx.array_sort(intSort(), bvSort()); }

z3::sort Z3Encoder::valueSort(const VType &Ty, VIntMode Mode) {
  if (Ty.Kind == VTypeKind::Bool)
    return boolSort();
  if (Mode == VIntMode::Machine)
    return Ctx.bv_sort(Ty.bvWidth());
  return intSort();
}

// Does the bound variable appear anywhere in E?
static bool exprContains(z3::expr E, unsigned BinderId, std::set<unsigned> &Seen) {
  if (E.id() == BinderId)
    return true;
  if (!E.is_app() || !Seen.insert(E.id()).second)
    return false;
  for (unsigned I = 0; I < E.num_args(); ++I)
    if (exprContains(E.arg(I), BinderId, Seen))
      return true;
  return false;
}

// Collect array `select` subterms of E that mention the bound variable. These
// are the natural triggers for a heap-range quantifier: instantiate the
// quantifier exactly when such a heap access appears in a query.
static void collectSelectTriggers(z3::expr E, unsigned BinderId,
                                   std::vector<z3::expr> &Out,
                                   std::set<unsigned> &Visited) {
  if (!E.is_app() || !Visited.insert(E.id()).second)
    return;
  if (E.decl().decl_kind() == Z3_OP_SELECT) {
    std::set<unsigned> S;
    if (exprContains(E, BinderId, S))
      Out.push_back(E);
  }
  for (unsigned I = 0; I < E.num_args(); ++I)
    collectSelectTriggers(E.arg(I), BinderId, Out, Visited);
}

// Widen a bit-vector to W bits (sign- or zero-extending). Used to reconcile
// mixed-width operands (e.g. int + long) before a bit-vector operation.
static z3::expr extendBV(z3::expr E, unsigned W, bool Signed) {
  if (!E.is_bv())
    return E;
  unsigned Cur = E.get_sort().bv_size();
  if (Cur >= W)
    return E;
  return Signed ? z3::sext(E, W - Cur) : z3::zext(E, W - Cur);
}

static std::string specZ3Name(const std::string &Fn, VIntMode Mode) {
  return "spec$" + Fn + (Mode == VIntMode::Machine ? "$bv" : "$int");
}

static std::string specDeclKey(const std::string &Fn, VIntMode Mode) {
  return Fn + (Mode == VIntMode::Machine ? "$bv" : "$int");
}

// A recursive spec function (proven terminating via `decreases`) is encoded with
// an explicit fuel argument so its defining axiom unfolds a bounded number of
// times. Non-recursive specs are fully inlined and need no fuel.
bool Z3Encoder::specIsRecursive(const VFunction *S) {
  return S && S->NeedsDecreasesCheck;
}

// Fuel is an uninterpreted sort with a zero constant and a successor function.
// Using uninterpreted Succ/Zero (rather than arithmetic) keeps the axiom
// triggers `f(Succ(g), args)` purely syntactic: a term at `f(Zero, args)` does
// not match, so unfolding halts exactly at the reveal depth and cannot loop.
z3::sort Z3Encoder::fuelSort() {
  if (!FuelSortOpt)
    FuelSortOpt = Ctx.uninterpreted_sort("Fuel");
  return *FuelSortOpt;
}
z3::func_decl Z3Encoder::fuelSucc() {
  if (!FuelSuccOpt)
    FuelSuccOpt = Ctx.function("$fuelS", fuelSort(), fuelSort());
  return *FuelSuccOpt;
}
z3::expr Z3Encoder::fuelZero() {
  if (!FuelZeroOpt)
    FuelZeroOpt = Ctx.constant("$fuelZ", fuelSort());
  return *FuelZeroOpt;
}
z3::expr Z3Encoder::fuelTerm(unsigned K) {
  z3::expr T = fuelZero();
  for (unsigned I = 0; I < K; ++I)
    T = fuelSucc()(T);
  return T;
}

z3::func_decl Z3Encoder::specFuncDecl(const VFunction *Spec) {
  assert(Spec && "specFuncDecl requires a spec function");
  std::string Key = specDeclKey(Spec->Name, CallerIntMode);
  auto It = SpecFuncDecls.find(Key);
  if (It != SpecFuncDecls.end())
    return It->second;
  std::vector<z3::sort> Domain;
  // Recursive specs carry a leading Fuel argument (bounds axiom unfolding).
  if (specIsRecursive(Spec))
    Domain.push_back(fuelSort());
  for (const auto &P : Spec->Params)
    Domain.push_back(valueSort(P.second, CallerIntMode));
  z3::sort Ret = valueSort(Spec->ReturnType, CallerIntMode);
  z3::func_decl F =
      Ctx.function(specZ3Name(Spec->Name, CallerIntMode).c_str(), Domain.size(),
                   Domain.data(), Ret);
  SpecFuncDecls.emplace(Key, F);
  return F;
}

z3::expr Z3Encoder::encodeVExprForAxiom(const VExpr *E, const VType &RetTy) {
  VCMachine M = VCMachine::fromVExpr(E, "", std::string(VHeapName) + "_0",
                                    CallerIntMode);
  if (!M.Goal)
    return RetTy.Kind == VTypeKind::Bool
               ? Ctx.bool_val(true)
               : (CallerIntMode == VIntMode::Machine ? Ctx.bv_val(0, 32)
                                                     : Ctx.int_val(0));
  return encodeVC(M.Goal.get());
}

z3::expr Z3Encoder::coerceTo(z3::expr E, VIntMode Target) {
  if (E.is_int() && Target == VIntMode::Math)
    return E;
  if (E.is_bv() && Target == VIntMode::Machine)
    return E;
  if (E.is_int() && Target == VIntMode::Machine)
    return z3::int2bv(32, E);
  if (E.is_bv() && Target == VIntMode::Math)
    return z3::bv2int(E, true);
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

static z3::expr asBool(z3::context &Ctx, z3::expr E) {
  if (E.is_bool())
    return E;
  if (E.get_sort().is_array())
    return Ctx.bool_val(true);
  if (E.is_int())
    return E != 0;
  if (E.is_bv())
    return E != 0;
  return Ctx.bool_val(true);
}

/// Heap is Array Int BitVec32. Indices are integer addresses; a bit-vector
/// pointer is widened to an integer key.
static z3::expr heapIndex(z3::expr Ptr) {
  // The heap is indexed by integer addresses. Pointer expressions are already
  // integers; coerce a bit-vector address (defensive) down to an integer.
  if (Ptr.is_bv())
    return z3::bv2int(Ptr, false);
  return Ptr;
}

/// Cell values are stored as 32-bit bit-vectors (machine integers); a
/// mathematical-integer value is converted on the way in.
static z3::expr heapCellValue(z3::expr Val) {
  if (Val.is_bv())
    return Val;
  if (Val.is_int())
    return z3::int2bv(32, Val);
  return Val;
}

static z3::expr arithOp(z3::context &Ctx, VCExpr::Kind K, z3::expr L, z3::expr R,
                        bool Unsigned = false) {
  if (L.get_sort().is_array() || R.get_sort().is_array()) {
    // Equality/inequality of heap arrays is meaningful (e.g. the if-merge
    // assume `mem_k == ite(c, mem_then, mem_else)`); only arithmetic on arrays
    // is not. Encoding array Eq as `true` left merged heaps unconstrained.
    if (K == VCExpr::Eq)
      return L == R;
    if (K == VCExpr::Ne)
      return L != R;
    return Ctx.bool_val(true);
  }
  if (L.is_bv() && R.is_int())
    R = z3::int2bv(L.get_sort().bv_size(), R);
  if (L.is_int() && R.is_bv())
    L = z3::int2bv(R.get_sort().bv_size(), L);
  // Reconcile mixed bit-vector widths (e.g. int32 + long64): extend the
  // narrower operand to the wider, signed unless the operation is unsigned.
  if (L.is_bv() && R.is_bv() && L.get_sort().bv_size() != R.get_sort().bv_size()) {
    unsigned W = std::max(L.get_sort().bv_size(), R.get_sort().bv_size());
    L = extendBV(L, W, !Unsigned);
    R = extendBV(R, W, !Unsigned);
  }
  switch (K) {
  case VCExpr::Add:
    return L + R;
  case VCExpr::Sub:
    return L - R;
  case VCExpr::Mul:
    return L * R;
  case VCExpr::Div:
    // Bit-vector: bvsdiv/bvudiv (operator/ is signed). Int mode: z3 integer div.
    if (L.is_bv())
      return Unsigned ? z3::udiv(L, R) : (L / R);
    return L / R;
  case VCExpr::Rem:
    // C++ % is the truncated remainder (sign of dividend) == bvsrem, NOT bvsmod.
    if (L.is_bv())
      return Unsigned ? z3::urem(L, R) : z3::srem(L, R);
    return z3::mod(L, R);
  case VCExpr::Lt:
    return L < R;
  case VCExpr::Le:
    return L <= R;
  case VCExpr::Gt:
    return L > R;
  case VCExpr::Ge:
    return L >= R;
  case VCExpr::Eq:
    return L == R;
  case VCExpr::Ne:
    return L != R;
  default:
    return L == R;
  }
}

z3::expr Z3Encoder::encodeVCNode(
    const VCExpr *E, const std::map<const VCExpr *, z3::expr> &Done) {
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
    if (E->IsPtr) // address literal (e.g. nullptr): integer
      return Ctx.int_val(static_cast<int64_t>(E->IntVal));
    if (E->IntMode == VIntMode::Machine)
      return Ctx.bv_val(static_cast<int64_t>(E->IntVal), E->Width);
    return Ctx.int_val(static_cast<int64_t>(E->IntVal));
  }
  case VCExpr::Var: {
    auto It = Vars.find(E->Name);
    if (It != Vars.end())
      return It->second;
    z3::expr Z = Ctx.int_const("_unused");
    if (E->Name.find("__heap") != std::string::npos ||
        E->Name.rfind(VHeapName, 0) == 0) {
      Z = Ctx.constant(E->Name.c_str(), heapSort());
    } else if (E->IsPtr) {
      Z = Ctx.int_const(E->Name.c_str()); // addresses are integers
    } else if (E->IntMode == VIntMode::Machine) {
      Z = Ctx.bv_const(E->Name.c_str(), E->Width);
    } else {
      Z = Ctx.int_const(E->Name.c_str());
    }
    Vars.emplace(E->Name, Z);
    return Z;
  }
  case VCExpr::IntToBv: {
    z3::expr Inner = child(0);
    if (Inner.is_int())
      return z3::int2bv(32, Inner);
    return Inner;
  }
  case VCExpr::BvToInt: {
    z3::expr Inner = child(0);
    if (Inner.is_bv())
      return z3::bv2int(Inner, true);
    return Inner;
  }
  case VCExpr::Not:
    return !asBool(Ctx, child(0));
  case VCExpr::And: {
    z3::expr_vector Ch(Ctx);
    for (const auto &C : E->Children) {
      if (!C)
        continue;
      z3::expr Elt = Done.at(C.get());
      if (Elt.is_bool())
        Ch.push_back(Elt);
      else if (!Elt.get_sort().is_array())
        Ch.push_back(asBool(Ctx, Elt));
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
        continue;
      z3::expr Elt = Done.at(C.get());
      if (Elt.is_bool())
        Ch.push_back(Elt);
      else if (!Elt.get_sort().is_array())
        Ch.push_back(asBool(Ctx, Elt));
    }
    if (Ch.empty())
      return Ctx.bool_val(false);
    if (Ch.size() == 1)
      return Ch[0];
    return z3::mk_or(Ch);
  }
  case VCExpr::Ite: {
    z3::expr C = asBool(Ctx, child(0));
    z3::expr T = coerceTo(child(1), E->IntMode);
    z3::expr F = coerceTo(child(2), E->IntMode);
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
  case VCExpr::Rem: {
    // Pointer arithmetic / comparison is done in (wrap-free) integer arithmetic;
    // the offset operand is coerced from its bit-vector to an integer.
    VIntMode Mode = E->IsPtr ? VIntMode::Math : E->IntMode;
    z3::expr L = coerceTo(child(0), Mode);
    z3::expr R = coerceTo(child(1), Mode);
    return arithOp(Ctx, E->K, L, R, E->Unsigned);
  }
  case VCExpr::Neg:
    return -coerceTo(child(0), E->IntMode);
  case VCExpr::NoOverflow: {
    // The signed Op of the (bit-vector) operands does not overflow. IntVal holds
    // the VOverflowOp. Operands are sign-extended to their common width
    // (e.g. int + long), computed from the *encoded* operands so a stripped
    // widening cast does not leave a mismatch.
    VOverflowOp Op = static_cast<VOverflowOp>(E->IntVal);
    z3::expr A0 = coerceTo(child(0), VIntMode::Machine);
    if (Op == VOverflowOp::Neg)
      return z3::bvneg_no_overflow(A0);
    z3::expr B0 = coerceTo(child(1), VIntMode::Machine);
    unsigned W = std::max({E->Width, A0.is_bv() ? A0.get_sort().bv_size() : 32u,
                           B0.is_bv() ? B0.get_sort().bv_size() : 32u});
    z3::expr A = extendBV(A0, W, true);
    z3::expr B = extendBV(B0, W, true);
    switch (Op) {
    case VOverflowOp::Add:
      return z3::bvadd_no_overflow(A, B, true) && z3::bvadd_no_underflow(A, B);
    case VOverflowOp::Sub:
      return z3::bvsub_no_overflow(A, B) && z3::bvsub_no_underflow(A, B, true);
    case VOverflowOp::Mul:
      return z3::bvmul_no_overflow(A, B, true) && z3::bvmul_no_underflow(A, B);
    case VOverflowOp::SDiv:
      return z3::bvsdiv_no_overflow(A, B);
    case VOverflowOp::Neg:
      break;
    }
    return Ctx.bool_val(true);
  }
  case VCExpr::Select: {
    z3::expr Val = z3::select(child(0), heapIndex(child(1)));
    return coerceTo(Val, E->IntMode);
  }
  case VCExpr::Store: {
    z3::expr Before = child(0);
    z3::expr Ptr = heapIndex(child(1));
    z3::expr Val = heapCellValue(child(2));
    z3::expr After = child(3);
    return (After == z3::store(Before, Ptr, Val));
  }
  case VCExpr::Forall: {
    // Real bounded quantifier: children are [lo, hi, body]; the binder is the
    // free bit-vector const the body was encoded against (the half-open bound is
    // the implicit trigger). forall i. lo <= i < hi => body;  exists: &&.
    z3::expr Lo = coerceTo(child(0), VIntMode::Machine);
    z3::expr Hi = coerceTo(child(1), VIntMode::Machine);
    z3::expr Body = asBool(Ctx, child(2));
    auto It = Vars.find(E->Binder);
    z3::expr I = It != Vars.end() ? It->second
                                  : Ctx.bv_const(E->Binder.c_str(), 32);
    // Build the range guard lo <= i < hi, reconciling the binder and bound
    // sorts. The binder is normally a 32-bit bit-vector, but address-typed
    // contexts can make it (or the bounds) integers; coerce everything to the
    // binder's sort so the comparison is well-typed.
    z3::expr Range(Ctx);
    if (I.is_bv()) {
      unsigned W = std::max({I.get_sort().bv_size(),
                             Lo.is_bv() ? Lo.get_sort().bv_size() : 32u,
                             Hi.is_bv() ? Hi.get_sort().bv_size() : 32u});
      z3::expr Ib = extendBV(I, W, true);
      auto toBV = [&](z3::expr E) {
        return E.is_bv() ? extendBV(E, W, true) : z3::int2bv(W, E);
      };
      Range = (Ib >= toBV(Lo)) && (Ib < toBV(Hi));
    } else {
      auto toInt = [&](z3::expr E) {
        return E.is_bv() ? z3::bv2int(E, true) : E;
      };
      Range = (I >= toInt(Lo)) && (I < toInt(Hi));
    }
    z3::expr Matrix = E->BoolVal ? z3::implies(Range, Body) : (Range && Body);

    // Emit a plain quantifier and let MBQI handle instantiation. Explicit
    // heap-access triggers were tried, but an over-restrictive pattern on a
    // goal-position forall makes the negated existential refutation incomplete
    // and Z3 can wrongly report unsat (unsound). With integer addresses MBQI
    // closes the cross-buffer goals on its own.
    std::vector<z3::expr> Trigs;
    std::set<unsigned> Visited;
    (void)collectSelectTriggers; // retained for future hypothesis-only triggering
    if (Trigs.empty())
      return E->BoolVal ? z3::forall(I, Matrix) : z3::exists(I, Matrix);

    std::vector<Z3_pattern> Pats;
    Pats.reserve(Trigs.size());
    for (z3::expr &T : Trigs) {
      Z3_ast Term = T;
      Pats.push_back(Z3_mk_pattern(Ctx, 1, &Term));
    }
    Z3_app Bound = reinterpret_cast<Z3_app>(static_cast<Z3_ast>(I));
    Z3_ast Q = E->BoolVal
                   ? Z3_mk_forall_const(Ctx, 0, 1, &Bound,
                                        static_cast<unsigned>(Pats.size()),
                                        Pats.data(), Matrix)
                   : Z3_mk_exists_const(Ctx, 0, 1, &Bound,
                                        static_cast<unsigned>(Pats.size()),
                                        Pats.data(), Matrix);
    return z3::expr(Ctx, Q);
  }
  case VCExpr::SpecCall: {
    auto It = SpecFunctions.find(E->SpecCallee);
    if (It == SpecFunctions.end() || !It->second)
      return Ctx.int_val(0);
    const VFunction *Spec = It->second;
    z3::func_decl F = specFuncDecl(Spec);
    std::vector<z3::expr> Args;
    if (specIsRecursive(Spec)) {
      // Choose the fuel for this application: a self-recursive call inside the
      // function's own defining axiom uses the (lowered) bound fuel variable;
      // any other site uses the reveal depth (default 1 for recursive specs).
      if (AxiomSelfSpec && AxiomSelfFuel &&
          E->SpecCallee == AxiomSelfSpec->Name)
        Args.push_back(*AxiomSelfFuel);
      else {
        unsigned K = 1;
        if (auto FI = SpecFuelMap.find(E->SpecCallee); FI != SpecFuelMap.end())
          K = FI->second ? FI->second : 1;
        Args.push_back(fuelTerm(K));
      }
    }
    for (unsigned i = 0; i < E->Children.size(); ++i)
      Args.push_back(coerceTo(child(i), CallerIntMode));
    z3::expr A = F(static_cast<unsigned>(Args.size()), Args.data());
    return coerceTo(A, CallerIntMode);
  }
  }
  return Ctx.bool_val(true);
}

z3::expr Z3Encoder::encodeVC(const VCExpr *Root) {
  if (!Root)
    return Ctx.bool_val(true);
  std::map<const VCExpr *, z3::expr> Done;
  std::vector<const VCExpr *> Stack = {Root};
  while (!Stack.empty()) {
    const VCExpr *E = Stack.back();
    if (Done.count(E)) {
      Stack.pop_back();
      continue;
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

void Z3Encoder::emitSpecDefiningAxiom(const std::string &Name,
                                      const SpecAxiomContext &ACtx) {
  auto It = ACtx.Functions.find(Name);
  if (It == ACtx.Functions.end() || !It->second)
    return;
  const VFunction &Spec = *It->second;

  // Recursive specs: emit a fuel-parameterized definition. With f a fresh fuel
  // variable and the function declared as F(Fuel, args):
  //   unfold:  forall f,a. {F(Succ(f),a)} F(Succ(f),a) == body[ rec g(x) := F(f,x) ]
  //   synonym: forall f,a. {F(Succ(f),a)} F(Succ(f),a) == F(f,a)
  // The shared trigger F(Succ(f),a) and uninterpreted Succ/Zero bound unfolding
  // to the reveal depth (a goal call is F(Succ^K(Zero),a)); the synonym lets a
  // term at higher fuel be lowered so the unfold leaves (at fuel f) meet the
  // goal's other calls. The recursive leaves stay the *same* function, so the
  // axiom genuinely pins F down (unlike fresh-constant leaves).
  if (specIsRecursive(&Spec)) {
    z3::func_decl Fdecl = specFuncDecl(&Spec);
    z3::expr FVar = Ctx.constant("$f", fuelSort());
    std::vector<z3::expr> ParamConsts;
    for (const auto &P : Spec.Params) {
      z3::expr V = CallerIntMode == VIntMode::Machine
                       ? Ctx.bv_const(P.first.c_str(), 32)
                       : Ctx.int_const(P.first.c_str());
      Vars.emplace(P.first, V);
      ParamConsts.push_back(V);
    }
    auto applyFuel = [&](z3::expr FuelArg) {
      std::vector<z3::expr> A;
      A.push_back(FuelArg);
      for (auto &C : ParamConsts)
        A.push_back(C);
      return Fdecl(static_cast<unsigned>(A.size()), A.data());
    };
    z3::expr LHS = applyFuel(fuelSucc()(FVar));
    z3::expr Lowered = applyFuel(FVar);

    std::unique_ptr<VExpr> Body = unfoldSpecBodyForAxiom(Spec, ACtx);
    AxiomSelfSpec = &Spec;
    AxiomSelfFuel = FVar;
    z3::expr RHS = Body ? encodeVExprForAxiom(Body.get(), Spec.ReturnType)
                        : Lowered;
    AxiomSelfSpec = nullptr;
    AxiomSelfFuel.reset();

    // forall [f, params] {LHS} (LHS == Matrix)
    auto quantWithTrigger = [&](z3::expr Matrix) {
      std::vector<Z3_app> Bound;
      Bound.push_back(reinterpret_cast<Z3_app>(static_cast<Z3_ast>(FVar)));
      for (auto &C : ParamConsts)
        Bound.push_back(reinterpret_cast<Z3_app>(static_cast<Z3_ast>(C)));
      Z3_ast PatTerm = LHS;
      Z3_pattern Pat = Z3_mk_pattern(Ctx, 1, &PatTerm);
      Z3_ast Q = Z3_mk_forall_const(Ctx, 0, static_cast<unsigned>(Bound.size()),
                                    Bound.data(), 1, &Pat, Matrix);
      return z3::expr(Ctx, Q);
    };
    Solver.add(quantWithTrigger(LHS == RHS));
    Solver.add(quantWithTrigger(LHS == Lowered));
    for (const auto &P : Spec.Params)
      Vars.erase(P.first);
    return;
  }

  unsigned Fuel = 0;
  if (ACtx.HiddenSpecs.count(Spec.Name))
    Fuel = 0;
  else if (auto F = ACtx.SpecFuel.find(Spec.Name); F != ACtx.SpecFuel.end())
    Fuel = F->second;
  else if (ACtx.RevealedSpecs.count(Spec.Name))
    Fuel = 1;
  else if (!Spec.NeedsDecreasesCheck)
    Fuel = 64;
  std::unique_ptr<VExpr> Body = unfoldSpecDefinition(Spec, ACtx, Fuel);
  if (!Body)
    return;
  z3::func_decl Fdecl = specFuncDecl(&Spec);
  z3::expr_vector ParamVars(Ctx);
  std::vector<z3::expr> AppArgs;
  for (const auto &P : Spec.Params) {
    z3::expr V = CallerIntMode == VIntMode::Machine
                     ? Ctx.bv_const(P.first.c_str(), 32)
                     : Ctx.int_const(P.first.c_str());
    Vars.emplace(P.first, V);
    ParamVars.push_back(V);
    AppArgs.push_back(V);
  }
  z3::expr LHS = Fdecl(static_cast<unsigned>(AppArgs.size()), AppArgs.data());
  z3::expr RHS = encodeVExprForAxiom(Body.get(), Spec.ReturnType);
  z3::expr Eq = (LHS == RHS);
  Solver.add(z3::forall(ParamVars, Eq));
  for (const auto &P : Spec.Params)
    Vars.erase(P.first);
}

VerifyResult Z3Encoder::verifyMachine(const VCMachine &M) {
  Vars.clear();
  Solver = z3::solver(Ctx);
  {
    z3::params P(Ctx);
    if (TimeoutMs > 0)
      P.set("timeout", TimeoutMs);
    // Model-based quantifier instantiation: a fallback when pattern-based
    // (e-matching) instantiation cannot close a goal involving quantifiers over
    // the heap and address arithmetic (e.g. cross-buffer non-overlap).
    P.set("mbqi", true);
    Solver.set(P);
  }
  SpecFunctions = M.SpecFunctions;
  SpecFuelMap = M.SpecFuel;
  CallerIntMode = M.CallerIntMode;
  VerifyResult Out;
  if (!M.Goal) {
    Out.Status = VerifyStatus::Verified;
    return Out;
  }
  SpecAxiomContext AxiomCtx{M.SpecFunctions, M.SpecFuel, M.HiddenSpecs,
                            M.RevealedSpecs, M.CallerIntMode};
  emitSpecAxioms(*this, M.Goal.get(), AxiomCtx);
  Vars.clear();
  Solver.add(encodeVC(M.Goal.get()));
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
    Out.Status = VerifyStatus::Unknown;
    return Out;
  }
}

void Z3Encoder::dumpVC(const VCExpr *E, llvm::raw_ostream &OS) {
  Z3Encoder Tmp;
  OS << Tmp.encodeVC(E).to_string() << "\n";
}

VerifyResult Z3VerifyBackend::verifyPassive(const PassiveProgram &P) {
  VCMachine M = VCMachine::fromPassive(P);
  VerifyResult R = Enc.verifyMachine(M);
  if (R.Status == VerifyStatus::Failed) {
    std::string Msg;
    for (const auto &KV : R.Model) {
      if (!Msg.empty())
        Msg += ", ";
      Msg += KV.first + " = " + KV.second;
    }
    R.Message = Msg;
  }
  return R;
}