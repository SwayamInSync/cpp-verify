//===--- Z3Encode.cpp -----------------------------------------------------===//
#include "Z3Encode.h"
#include "llvm/Support/raw_ostream.h"

using namespace clang;
using namespace verify;

template <typename T, typename U> static const T *cast(const U *p) {
  return static_cast<const T *>(p);
}

Z3Encoder::Z3Encoder() : Ctx(), Solver(Ctx) {}

z3::sort Z3Encoder::intSort() { return Ctx.int_sort(); }
z3::sort Z3Encoder::boolSort() { return Ctx.bool_sort(); }

z3::expr Z3Encoder::encodeExpr(const VExpr *E) {
  if (!E)
    return Ctx.bool_val(true);
  switch (E->K) {
  case VExpr::Literal: {
    const auto *L = static_cast<const VLiteralExpr *>(E);
    if (L->Ty.Kind == VTypeKind::Bool)
      return Ctx.bool_val(L->Value != 0);
    return Ctx.int_val(static_cast<int>(L->Value));
  }
  case VExpr::Var: {
    const auto *V = static_cast<const VVarExpr *>(E);
    auto It = Vars.find(V->Name);
    if (It != Vars.end())
      return It->second;
    z3::expr Z = (V->Ty.Kind == VTypeKind::Bool) ? Ctx.bool_const(V->Name.c_str())
                                                  : Ctx.int_const(V->Name.c_str());
    Vars.insert({V->Name, Z});
    return Z;
  }
  case VExpr::BinOp: {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    z3::expr L = encodeExpr(B->Lhs.get());
    z3::expr R = encodeExpr(B->Rhs.get());
    switch (B->Op) {
    case VBinOp::Add: return L + R;
    case VBinOp::Sub: return L - R;
    case VBinOp::Mul: return L * R;
    case VBinOp::Lt: return L < R;
    case VBinOp::Le: return L <= R;
    case VBinOp::Gt: return L > R;
    case VBinOp::Ge: return L >= R;
    case VBinOp::Eq: return L == R;
    case VBinOp::Ne: return L != R;
    case VBinOp::And: return L && R;
    case VBinOp::Or: return L || R;
    default: return L == R;
    }
  }
  case VExpr::UnaryOp: {
    const auto *U = static_cast<const VUnaryOpExpr *>(E);
    z3::expr O = encodeExpr(U->Operand.get());
    if (U->Op == VUnaryOp::Neg)
      return -O;
    return !O;
  }
  case VExpr::Conditional: {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    return z3::ite(encodeExpr(C->Cond.get()), encodeExpr(C->Then.get()),
                   encodeExpr(C->Else.get()));
  }
  case VExpr::Result:
    return Ctx.int_const("__result_0");
  case VExpr::Old:
    return encodeExpr(static_cast<const VOldExpr *>(E)->Inner.get());
  case VExpr::Cast:
    return encodeExpr(static_cast<const VCastExpr *>(E)->Inner.get());
  case VExpr::Load:
    return encodeExpr(static_cast<const VLoadExpr *>(E)->Ptr.get());
  }
  return Ctx.bool_val(true);
}

void Z3Encoder::dumpVC(const VExpr *VC, llvm::raw_ostream &OS) {
  Z3Encoder Tmp;
  OS << Tmp.encodeExpr(VC).to_string() << "\n";
}

Z3CheckResult Z3Encoder::checkVC(const VExpr *VC) {
  Vars.clear();
  Solver = z3::solver(Ctx);
  Z3CheckResult Out;
  z3::expr F = encodeExpr(VC);
  Solver.add(F);
  switch (Solver.check()) {
  case z3::unsat:
    Out.S = Z3CheckResult::Verified;
    return Out;
  case z3::sat: {
    Out.S = Z3CheckResult::Failed;
    z3::model M = Solver.get_model();
    std::string Msg;
    for (auto &KV : Vars) {
      z3::expr Val = M.eval(KV.second, true);
      if (Msg.empty())
        Msg = KV.first + " = " + Val.to_string();
      else
        Msg += ", " + KV.first + " = " + Val.to_string();
    }
    Out.Counterexample = Msg;
    return Out;
  }
  default:
    Out.S = Z3CheckResult::Unknown;
    return Out;
  }
}