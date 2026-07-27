//===--- DumpIR.cpp -------------------------------------------------------===//
#include "DumpIR.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/raw_ostream.h"

using namespace clang;
using namespace verify;

unsigned verify::parseDumpIRLayers(llvm::StringRef Spec) {
  Spec = Spec.trim();
  if (Spec.empty() || Spec.equals_insensitive("all"))
    return LayerAll;

  unsigned Mask = 0;
  while (!Spec.empty()) {
    llvm::StringRef Tok;
    std::tie(Tok, Spec) = Spec.split(',');
    Tok = Tok.trim();
    Spec = Spec.trim();
    if (Tok.empty())
      continue;
    if (Tok.equals_insensitive("layer-1") || Tok == "1")
      Mask |= LayerVCR;
    else if (Tok.equals_insensitive("layer-2") || Tok == "2")
      Mask |= LayerPassive;
    else if (Tok.equals_insensitive("layer-3") || Tok == "3")
      Mask |= LayerVC;
    else if (Tok.equals_insensitive("layer-4") || Tok == "4")
      Mask |= LayerZ3;
  }
  return Mask;
}

static llvm::raw_ostream &ind(llvm::raw_ostream &OS, unsigned N) {
  for (unsigned I = 0; I < N; ++I)
    OS << "  ";
  return OS;
}

static const char *binOpToken(VBinOp Op) {
  switch (Op) {
  case VBinOp::Add:
    return "+";
  case VBinOp::Sub:
    return "-";
  case VBinOp::Mul:
    return "*";
  case VBinOp::Div:
    return "/";
  case VBinOp::Rem:
    return "%";
  case VBinOp::BitAnd:
    return "&";
  case VBinOp::BitOr:
    return "|";
  case VBinOp::BitXor:
    return "^";
  case VBinOp::Shl:
    return "<<";
  case VBinOp::Shr:
    return ">>";
  case VBinOp::Lt:
    return "<";
  case VBinOp::Le:
    return "<=";
  case VBinOp::Gt:
    return ">";
  case VBinOp::Ge:
    return ">=";
  case VBinOp::Eq:
    return "==";
  case VBinOp::Ne:
    return "!=";
  case VBinOp::And:
    return "&&";
  case VBinOp::Or:
    return "||";
  }
  return "==";
}

void verify::dumpVExpr(const VExpr *E, llvm::raw_ostream &OS, unsigned Depth) {
  if (!E) {
    ind(OS, Depth) << "_\n";
    return;
  }
  ind(OS, Depth);
  switch (E->K) {
  case VExpr::Literal: {
    const auto *L = static_cast<const VLiteralExpr *>(E);
    if (L->Ty.Kind == VTypeKind::Bool)
      OS << (L->Value != "0" ? "true" : "false");
    else
      OS << L->Value;
    OS << "\n";
    break;
  }
  case VExpr::Var:
    OS << static_cast<const VVarExpr *>(E)->Name << "\n";
    break;
  case VExpr::BinOp: {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    OS << binOpToken(B->Op) << "\n";
    dumpVExpr(B->Lhs.get(), OS, Depth + 1);
    dumpVExpr(B->Rhs.get(), OS, Depth + 1);
    break;
  }
  case VExpr::UnaryOp: {
    const auto *U = static_cast<const VUnaryOpExpr *>(E);
    OS << (U->Op == VUnaryOp::Neg        ? "-"
           : U->Op == VUnaryOp::Not      ? "!"
           : U->Op == VUnaryOp::BitNot   ? "~"
           : U->Op == VUnaryOp::ValidPtr ? "valid_ptr"
                                         : "initialized_ptr")
       << "\n";
    dumpVExpr(U->Operand.get(), OS, Depth + 1);
    break;
  }
  case VExpr::Cast:
    OS << "cast\n";
    dumpVExpr(static_cast<const VCastExpr *>(E)->Inner.get(), OS, Depth + 1);
    break;
  case VExpr::Load:
    OS << "load\n";
    dumpVExpr(static_cast<const VLoadExpr *>(E)->Ptr.get(), OS, Depth + 1);
    break;
  case VExpr::Result:
    OS << "result\n";
    break;
  case VExpr::Old:
    OS << "old\n";
    dumpVExpr(static_cast<const VOldExpr *>(E)->Inner.get(), OS, Depth + 1);
    break;
  case VExpr::Conditional:
    OS << "ite\n";
    dumpVExpr(static_cast<const VConditionalExpr *>(E)->Cond.get(), OS,
              Depth + 1);
    dumpVExpr(static_cast<const VConditionalExpr *>(E)->Then.get(), OS,
              Depth + 1);
    dumpVExpr(static_cast<const VConditionalExpr *>(E)->Else.get(), OS,
              Depth + 1);
    break;
  case VExpr::Forall:
    OS << "forall " << static_cast<const VQuantifiedExpr *>(E)->Binder << "\n";
    dumpVExpr(static_cast<const VQuantifiedExpr *>(E)->Lo.get(), OS, Depth + 1);
    dumpVExpr(static_cast<const VQuantifiedExpr *>(E)->Hi.get(), OS, Depth + 1);
    dumpVExpr(static_cast<const VQuantifiedExpr *>(E)->Body.get(), OS,
              Depth + 1);
    break;
  case VExpr::Exists:
    OS << "exists " << static_cast<const VQuantifiedExpr *>(E)->Binder << "\n";
    dumpVExpr(static_cast<const VQuantifiedExpr *>(E)->Lo.get(), OS, Depth + 1);
    dumpVExpr(static_cast<const VQuantifiedExpr *>(E)->Hi.get(), OS, Depth + 1);
    dumpVExpr(static_cast<const VQuantifiedExpr *>(E)->Body.get(), OS,
              Depth + 1);
    break;
  case VExpr::HeapStore:
    OS << "heap_store\n";
    break;
  case VExpr::FieldAccess: {
    const auto *F = static_cast<const VFieldAccessExpr *>(E);
    OS << "field " << F->Field << "\n";
    dumpVExpr(F->Base.get(), OS, Depth + 1);
    break;
  }
  case VExpr::SpecCall: {
    const auto *C = static_cast<const VSpecCallExpr *>(E);
    OS << "spec_call " << C->Callee << "\n";
    for (const auto &A : C->Args)
      dumpVExpr(A.get(), OS, Depth + 1);
    break;
  }
  case VExpr::OverflowCheck: {
    const auto *O = static_cast<const VOverflowCheckExpr *>(E);
    static const char *Names[] = {"add", "sub", "mul", "neg", "sdiv"};
    OS << "no-overflow." << Names[static_cast<int>(O->Op)] << "\n";
    dumpVExpr(O->Lhs.get(), OS, Depth + 1);
    if (O->Rhs)
      dumpVExpr(O->Rhs.get(), OS, Depth + 1);
    break;
  }
  }
}

static void dumpVStmt(const VStmt &S, llvm::raw_ostream &OS, unsigned Depth) {
  ind(OS, Depth);
  switch (S.K) {
  case VStmt::Assign: {
    const auto &A = static_cast<const VAssignStmt &>(S);
    OS << "assign " << A.Target << "\n";
    dumpVExpr(A.Value.get(), OS, Depth + 1);
    break;
  }
  case VStmt::Store: {
    const auto &St = static_cast<const VStoreStmt &>(S);
    OS << "store\n";
    dumpVExpr(St.Ptr.get(), OS, Depth + 1);
    dumpVExpr(St.Value.get(), OS, Depth + 1);
    break;
  }
  case VStmt::Allocate: {
    const auto &A = static_cast<const VAllocateStmt &>(S);
    OS << (A.IsAutomatic ? "stack_allocate " : "allocate ") << A.Target
       << " size " << A.SizeBytes << " align " << A.AlignBytes << " provenance "
       << A.ProvenanceTarget << "\n";
    if (A.Initializer)
      dumpVExpr(A.Initializer.get(), OS, Depth + 1);
    break;
  }
  case VStmt::Free:
    OS << "free\n";
    dumpVExpr(static_cast<const VFreeStmt &>(S).Ptr.get(), OS, Depth + 1);
    break;
  case VStmt::If: {
    const auto &I = static_cast<const VIfStmt &>(S);
    OS << "if\n";
    dumpVExpr(I.Cond.get(), OS, Depth + 1);
    for (const auto &T : I.Then)
      dumpVStmt(*T, OS, Depth + 1);
    for (const auto &E : I.Else)
      dumpVStmt(*E, OS, Depth + 1);
    break;
  }
  case VStmt::Return: {
    const auto &R = static_cast<const VReturnStmt &>(S);
    OS << "return\n";
    dumpVExpr(R.Value.get(), OS, Depth + 1);
    break;
  }
  case VStmt::While: {
    const auto &W = static_cast<const VWhileStmt &>(S);
    OS << "while\n";
    dumpVExpr(W.Cond.get(), OS, Depth + 1);
    for (const auto &Inv : W.Invariants)
      dumpVExpr(Inv.get(), OS, Depth + 1);
    for (const auto &D : W.Decreases)
      dumpVExpr(D.get(), OS, Depth + 1);
    for (const auto &B : W.Body)
      dumpVStmt(*B, OS, Depth + 1);
    break;
  }
  case VStmt::Call: {
    const auto &C = static_cast<const VCallStmt &>(S);
    OS << "call " << C.Callee;
    if (!C.ResultTarget.empty())
      OS << " -> " << C.ResultTarget;
    if (!C.ResultProvenanceTarget.empty())
      OS << " provenance " << C.ResultProvenanceTarget;
    OS << "\n";
    for (const auto &Arg : C.Args)
      dumpVExpr(Arg.get(), OS, Depth + 1);
    break;
  }
  case VStmt::Assert:
    OS << "assert\n";
    dumpVExpr(static_cast<const VAssertStmt &>(S).Cond.get(), OS, Depth + 1);
    break;
  case VStmt::Assume:
    OS << "assume\n";
    dumpVExpr(static_cast<const VAssumeStmt &>(S).Cond.get(), OS, Depth + 1);
    break;
  case VStmt::Havoc:
    OS << "havoc " << static_cast<const VHavocStmt &>(S).Target << "\n";
    break;
  case VStmt::Seq:
    for (const auto &C : static_cast<const VSeqStmt &>(S).Stmts)
      dumpVStmt(*C, OS, Depth);
    break;
  case VStmt::GhostBlock: {
    OS << "ghost\n";
    for (const auto &B : static_cast<const VGhostBlockStmt &>(S).Body)
      dumpVStmt(*B, OS, Depth + 1);
    break;
  }
  case VStmt::ContractAssert:
    OS << "contract_assert\n";
    dumpVExpr(static_cast<const VContractAssertStmt &>(S).Cond.get(), OS,
              Depth + 1);
    break;
  case VStmt::RevealWithFuel:
    OS << "reveal_with_fuel\n";
    break;
  case VStmt::HideSpec:
    OS << "hide_spec\n";
    break;
  case VStmt::RevealSpec:
    OS << "reveal_spec\n";
    break;
  default:
    break;
  }
}

void verify::dumpVFunction(const VFunction &Fn, llvm::raw_ostream &OS) {
  ind(OS, 0) << "fn " << Fn.Name << "\n";
  if (Fn.IntMode == VIntMode::Math)
    ind(OS, 1) << "int math\n";
  for (const auto &P : Fn.Params)
    ind(OS, 1) << "param " << P.first << "\n";
  ind(OS, 1) << "pre\n";
  for (const auto &Pre : Fn.Preconditions)
    dumpVExpr(Pre.get(), OS, 2);
  ind(OS, 1) << "post\n";
  for (const auto &Post : Fn.Postconditions)
    dumpVExpr(Post.get(), OS, 2);
  ind(OS, 1) << "modifies\n";
  for (const auto &Modifies : Fn.Modifies)
    dumpVExpr(Modifies.get(), OS, 2);
  ind(OS, 1) << "body\n";
  for (const auto &S : Fn.Body)
    dumpVStmt(*S, OS, 2);
}

void verify::dumpPassiveProgram(llvm::StringRef FnName, const PassiveProgram &P,
                                llvm::raw_ostream &OS) {
  ind(OS, 0) << "passive " << FnName << "\n";
  if (!P.ResultVarName.empty())
    ind(OS, 1) << "result " << P.ResultVarName << "\n";
  ind(OS, 1) << "entry\n";
  for (const auto &A : P.EntryAssumes)
    dumpVExpr(A.get(), OS, 2);
  ind(OS, 1) << "stmt\n";
  for (const auto &S : P.Stmts) {
    ind(OS, 2) << (S->K == PassiveStmt::Assume ? "assume" : "assert") << "\n";
    dumpVExpr(S->Cond.get(), OS, 3);
  }
  ind(OS, 1) << "exit\n";
  for (const auto &A : P.ExitAsserts)
    dumpVExpr(A.get(), OS, 2);
}

static const char *logicExprToken(LogicExpr::Kind Kind) {
  switch (Kind) {
  case LogicExpr::True:
    return "true";
  case LogicExpr::False:
    return "false";
  case LogicExpr::IntLit:
    return "integer";
  case LogicExpr::BoolLit:
    return "boolean";
  case LogicExpr::Var:
    return "variable";
  case LogicExpr::Not:
    return "!";
  case LogicExpr::And:
    return "&&";
  case LogicExpr::Or:
    return "||";
  case LogicExpr::Ite:
    return "ite";
  case LogicExpr::Eq:
    return "==";
  case LogicExpr::Ne:
    return "!=";
  case LogicExpr::Lt:
    return "<";
  case LogicExpr::Le:
    return "<=";
  case LogicExpr::Gt:
    return ">";
  case LogicExpr::Ge:
    return ">=";
  case LogicExpr::Add:
    return "+";
  case LogicExpr::Sub:
    return "-";
  case LogicExpr::Mul:
    return "*";
  case LogicExpr::Div:
    return "/";
  case LogicExpr::Rem:
    return "%";
  case LogicExpr::Neg:
    return "neg";
  case LogicExpr::BitAnd:
    return "&";
  case LogicExpr::BitOr:
    return "|";
  case LogicExpr::BitXor:
    return "^";
  case LogicExpr::Shl:
    return "<<";
  case LogicExpr::Shr:
    return ">>";
  case LogicExpr::BitNot:
    return "~";
  case LogicExpr::ValidPtr:
    return "valid_ptr";
  case LogicExpr::Select:
    return "heap_select";
  case LogicExpr::Store:
    return "heap_store";
  case LogicExpr::Forall:
    return "forall";
  case LogicExpr::Exists:
    return "exists";
  case LogicExpr::IntToBv:
    return "int_to_bv";
  case LogicExpr::BvToInt:
    return "bv_to_int";
  case LogicExpr::BvResize:
    return "bv_resize";
  case LogicExpr::NoOverflow:
    return "no_overflow";
  case LogicExpr::SpecCall:
    return "spec_call";
  }
  return "unknown";
}

static void dumpLogicSort(const LogicSort &Sort, llvm::raw_ostream &OS) {
  OS << logicSortName(Sort.Kind);
  if (Sort.Kind == LogicSortKind::BitVector)
    OS << Sort.BitWidth;
}

static void dumpLogicExpr(const LogicExpr *Expr, llvm::raw_ostream &OS,
                          unsigned Depth) {
  if (!Expr) {
    ind(OS, Depth) << "_ : invalid\n";
    return;
  }
  ind(OS, Depth);
  if (Expr->K == LogicExpr::IntLit)
    OS << Expr->IntVal;
  else if (Expr->K == LogicExpr::BoolLit)
    OS << (Expr->BoolVal ? "true" : "false");
  else if (Expr->K == LogicExpr::Var)
    OS << Expr->Name;
  else if (Expr->K == LogicExpr::Forall || Expr->K == LogicExpr::Exists)
    OS << logicExprToken(Expr->K) << " " << Expr->Binder;
  else if (Expr->K == LogicExpr::SpecCall)
    OS << logicExprToken(Expr->K) << " " << Expr->SpecCallee;
  else
    OS << logicExprToken(Expr->K);
  OS << " : ";
  dumpLogicSort(Expr->Sort, OS);
  OS << "\n";
  for (const auto &Child : Expr->Children)
    dumpLogicExpr(Child.get(), OS, Depth + 1);
}

void verify::dumpVC(const ObligationModule &Module, llvm::raw_ostream &OS) {
  ind(OS, 0) << "vc " << Module.FunctionName << "\n";
  ind(OS, 1) << "identity " << Module.FunctionIdentity << "\n";
  ind(OS, 1) << "features " << formatLogicFeatures(Module.RequiredFeatures)
             << "\n";
  ind(OS, 1) << "counterexample\n";
  dumpLogicExpr(Module.CounterexampleQuery.get(), OS, 2);
  ind(OS, 1) << "obligations " << Module.Obligations.size() << "\n";
  for (const Obligation &Item : Module.Obligations) {
    ind(OS, 2) << "obligation " << Item.Id << " "
               << (Item.Kind == ObligationKind::Assertion ? "assertion"
                                                          : "postcondition")
               << "\n";
    ind(OS, 3) << "source "
               << (Item.Loc.isValid()
                       ? std::to_string(Item.Loc.getRawEncoding())
                       : "unknown")
               << "\n";
    ind(OS, 3) << "counterexample\n";
    dumpLogicExpr(Item.CounterexampleQuery.get(), OS, 4);
  }
}