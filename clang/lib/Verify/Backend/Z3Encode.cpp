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
z3::sort Z3Encoder::heapSort() { return Ctx.array_sort(intSort(), bvSort()); }

z3::sort Z3Encoder::valueSort(const VType &Ty, VIntMode Mode) {
  if (Ty.Kind == VTypeKind::Bool)
    return boolSort();
  if (Mode == VIntMode::Machine)
    return bvSort();
  return intSort();
}

static std::string specZ3Name(const std::string &Fn, VIntMode Mode) {
  return "spec$" + Fn + (Mode == VIntMode::Machine ? "$bv" : "$int");
}

static std::string specDeclKey(const std::string &Fn, VIntMode Mode) {
  return Fn + (Mode == VIntMode::Machine ? "$bv" : "$int");
}

z3::func_decl Z3Encoder::specFuncDecl(const VFunction *Spec) {
  assert(Spec && "specFuncDecl requires a spec function");
  std::string Key = specDeclKey(Spec->Name, CallerIntMode);
  auto It = SpecFuncDecls.find(Key);
  if (It != SpecFuncDecls.end())
    return It->second;
  std::vector<z3::sort> Domain;
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
  if (Ptr.is_bv())
    return z3::bv2int(Ptr, true);
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

static z3::expr arithOp(z3::context &Ctx, VCExpr::Kind K, z3::expr L, z3::expr R) {
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
    R = z3::int2bv(32, R);
  if (L.is_int() && R.is_bv())
    L = z3::int2bv(32, L);
  switch (K) {
  case VCExpr::Add:
    return L + R;
  case VCExpr::Sub:
    return L - R;
  case VCExpr::Mul:
    return L * R;
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
    if (E->IntMode == VIntMode::Machine)
      return Ctx.bv_val(static_cast<unsigned>(E->IntVal), 32);
    return Ctx.int_val(static_cast<int>(E->IntVal));
  }
  case VCExpr::Var: {
    auto It = Vars.find(E->Name);
    if (It != Vars.end())
      return It->second;
    z3::expr Z = Ctx.int_const("_unused");
    if (E->Name.find("__heap") != std::string::npos ||
        E->Name.rfind(VHeapName, 0) == 0) {
      Z = Ctx.constant(E->Name.c_str(), heapSort());
    } else if (E->IntMode == VIntMode::Machine) {
      Z = Ctx.bv_const(E->Name.c_str(), 32);
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
  case VCExpr::Mul: {
    z3::expr L = coerceTo(child(0), E->IntMode);
    z3::expr R = coerceTo(child(1), E->IntMode);
    return arithOp(Ctx, E->K, L, R);
  }
  case VCExpr::Neg:
    return -coerceTo(child(0), E->IntMode);
  case VCExpr::NoOverflow: {
    // The signed Op of the (bit-vector) operands does not overflow. IntVal
    // holds the VOverflowOp. Always reasons in bit-vector mode.
    z3::expr A = coerceTo(child(0), VIntMode::Machine);
    switch (static_cast<VOverflowOp>(E->IntVal)) {
    case VOverflowOp::Neg:
      return z3::bvneg_no_overflow(A);
    case VOverflowOp::Add: {
      z3::expr B = coerceTo(child(1), VIntMode::Machine);
      return z3::bvadd_no_overflow(A, B, true) && z3::bvadd_no_underflow(A, B);
    }
    case VOverflowOp::Sub: {
      z3::expr B = coerceTo(child(1), VIntMode::Machine);
      return z3::bvsub_no_overflow(A, B) && z3::bvsub_no_underflow(A, B, true);
    }
    case VOverflowOp::Mul: {
      z3::expr B = coerceTo(child(1), VIntMode::Machine);
      return z3::bvmul_no_overflow(A, B, true) && z3::bvmul_no_underflow(A, B);
    }
    case VOverflowOp::SDiv: {
      z3::expr B = coerceTo(child(1), VIntMode::Machine);
      return z3::bvsdiv_no_overflow(A, B);
    }
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
  case VCExpr::Forall:
    return Ctx.bool_val(true);
  case VCExpr::SpecCall: {
    auto It = SpecFunctions.find(E->SpecCallee);
    if (It == SpecFunctions.end() || !It->second)
      return Ctx.int_val(0);
    z3::func_decl F = specFuncDecl(It->second);
    std::vector<z3::expr> Args;
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
  if (TimeoutMs > 0) {
    z3::params P(Ctx);
    P.set("timeout", TimeoutMs);
    Solver.set(P);
  }
  SpecFunctions = M.SpecFunctions;
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