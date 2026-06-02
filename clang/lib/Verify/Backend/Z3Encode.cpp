//===--- Z3Encode.cpp -----------------------------------------------------===//
#include "Z3Encode.h"
#include "llvm/Support/raw_ostream.h"

using namespace clang;
using namespace verify;

Z3Encoder::Z3Encoder() : Ctx(), Solver(Ctx) {}

z3::sort Z3Encoder::intSort() { return Ctx.int_sort(); }
z3::sort Z3Encoder::boolSort() { return Ctx.bool_sort(); }
z3::sort Z3Encoder::heapSort() { return Ctx.array_sort(intSort(), intSort()); }

z3::expr Z3Encoder::heapVar(const std::string &Name) {
  auto It = Vars.find(Name);
  if (It != Vars.end())
    return It->second;
  z3::expr H = Ctx.constant(Name.c_str(), heapSort());
  Vars.emplace(Name, H);
  return H;
}

static int64_t evalIntLiteral(const VExpr *E) {
  if (!E || E->K != VExpr::Literal)
    return 0;
  return static_cast<const VLiteralExpr *>(E)->Value;
}

z3::expr Z3Encoder::expandQuantifier(const VQuantifiedExpr *Q, bool IsForall) {
  int64_t Lo = evalIntLiteral(Q->Lo.get());
  int64_t Hi = evalIntLiteral(Q->Hi.get());
  if (Hi <= Lo)
    return Ctx.bool_val(IsForall);
  z3::expr Acc = Ctx.bool_val(IsForall);
  for (int64_t I = Lo; I < Hi; ++I) {
    Vars.emplace(Q->Binder, Ctx.int_val(static_cast<int>(I)));
    z3::expr Body = encodeExpr(Q->Body.get(), std::string(VHeapName) + "_0");
    Acc = IsForall ? (Acc && Body) : (Acc || Body);
    Vars.erase(Q->Binder);
  }
  return Acc;
}

z3::expr Z3Encoder::encodeHeapStore(const VHeapStoreExpr *H) {
  z3::expr Before = heapVar(H->HeapBefore);
  z3::expr After = heapVar(H->HeapAfter);
  z3::expr Ptr = encodeExpr(H->Ptr.get(), H->HeapBefore);
  z3::expr Val = encodeExpr(H->Val.get(), H->HeapBefore);
  return After == z3::store(Before, Ptr, Val);
}

z3::expr Z3Encoder::encodeExpr(const VExpr *E, const std::string &CurHeap) {
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
    z3::expr Z = (V->Ty.Kind == VTypeKind::Bool)
                     ? Ctx.bool_const(V->Name.c_str())
                     : Ctx.int_const(V->Name.c_str());
    Vars.emplace(V->Name, Z);
    return Z;
  }
  case VExpr::BinOp: {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    z3::expr L = encodeExpr(B->Lhs.get(), CurHeap);
    z3::expr R = encodeExpr(B->Rhs.get(), CurHeap);
    switch (B->Op) {
    case VBinOp::Add:
      return L + R;
    case VBinOp::Sub:
      return L - R;
    case VBinOp::Mul:
      return L * R;
    case VBinOp::Lt:
      return L < R;
    case VBinOp::Le:
      return L <= R;
    case VBinOp::Gt:
      return L > R;
    case VBinOp::Ge:
      return L >= R;
    case VBinOp::Eq:
      return L == R;
    case VBinOp::Ne:
      return L != R;
    case VBinOp::And:
      return L && R;
    case VBinOp::Or:
      return L || R;
    default:
      return L == R;
    }
  }
  case VExpr::UnaryOp: {
    const auto *U = static_cast<const VUnaryOpExpr *>(E);
    z3::expr O = encodeExpr(U->Operand.get(), CurHeap);
    if (U->Op == VUnaryOp::Neg)
      return -O;
    return !O;
  }
  case VExpr::Conditional: {
    const auto *C = static_cast<const VConditionalExpr *>(E);
    return z3::ite(encodeExpr(C->Cond.get(), CurHeap),
                   encodeExpr(C->Then.get(), CurHeap),
                   encodeExpr(C->Else.get(), CurHeap));
  }
  case VExpr::Result: {
    const char *Name = ResultVarName.empty() ? "__result_0" : ResultVarName.c_str();
    auto It = Vars.find(Name);
    if (It != Vars.end())
      return It->second;
    z3::expr R = Ctx.int_const(Name);
    Vars.emplace(std::string(Name), R);
    return R;
  }
  case VExpr::Old:
    return encodeExpr(static_cast<const VOldExpr *>(E)->Inner.get(), CurHeap);
  case VExpr::Cast:
    return encodeExpr(static_cast<const VCastExpr *>(E)->Inner.get(), CurHeap);
  case VExpr::Load: {
    const auto *L = static_cast<const VLoadExpr *>(E);
    std::string Heap = L->HeapVar.empty() ? CurHeap : L->HeapVar;
    z3::expr H = heapVar(Heap);
    z3::expr Ptr = encodeExpr(L->Ptr.get(), Heap);
    return z3::select(H, Ptr);
  }
  case VExpr::Forall:
    return expandQuantifier(static_cast<const VQuantifiedExpr *>(E), true);
  case VExpr::Exists:
    return expandQuantifier(static_cast<const VQuantifiedExpr *>(E), false);
  case VExpr::HeapStore:
    return encodeHeapStore(static_cast<const VHeapStoreExpr *>(E));
  }
  return Ctx.bool_val(true);
}

Z3CheckResult Z3Encoder::verifyPassive(const PassiveProgram &P) {
  Vars.clear();
  Solver = z3::solver(Ctx);
  Z3CheckResult Out;
  ResultVarName = P.ResultVarName;

  std::string CurHeap = P.OldHeapName.empty() ? std::string(VHeapName) + "_0" : P.OldHeapName;
  z3::expr Hyp = Ctx.bool_val(true);
  z3::expr Post = Ctx.bool_val(true);

  for (const auto &A : P.EntryAssumes)
    Hyp = Hyp && encodeExpr(A.get(), CurHeap);

  for (const auto &S : P.Stmts) {
    if (S->K == PassiveStmt::Assume && S->Cond) {
      if (S->Cond->K == VExpr::HeapStore) {
        auto *H = static_cast<const VHeapStoreExpr *>(S->Cond.get());
        Hyp = Hyp && encodeHeapStore(H);
        CurHeap = H->HeapAfter;
      } else {
        Hyp = Hyp && encodeExpr(S->Cond.get(), CurHeap);
      }
    } else if (S->K == PassiveStmt::Assert && S->Cond) {
      Post = Post && encodeExpr(S->Cond.get(), CurHeap);
    }
  }

  for (const auto &A : P.ExitAsserts)
    Post = Post && encodeExpr(A.get(), CurHeap);

  Solver.add(Hyp && !Post);
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
      if (!Msg.empty())
        Msg += ", ";
      Msg += KV.first + " = " + Val.to_string();
    }
    Out.Counterexample = Msg;
    return Out;
  }
  default:
    Out.S = Z3CheckResult::Unknown;
    return Out;
  }
}

void Z3Encoder::dumpVC(const VExpr *VC, llvm::raw_ostream &OS) {
  Z3Encoder Tmp;
  OS << Tmp.encodeExpr(VC, std::string(VHeapName) + "_0").to_string() << "\n";
}

Z3CheckResult Z3Encoder::checkVC(const VExpr *VC) {
  Vars.clear();
  Solver = z3::solver(Ctx);
  Z3CheckResult Out;
  z3::expr F = encodeExpr(VC, std::string(VHeapName) + "_0");
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
      if (!Msg.empty())
        Msg += ", ";
      Msg += KV.first + " = " + Val.to_string();
    }
    Out.Counterexample = Msg;
    return Out;
  }
  default:
    Out.S = Z3CheckResult::Unknown;
    return Out;
  }
}