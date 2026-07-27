//===--- LeanBackend.cpp --------------------------------------------------===//
#include "LeanBackend.h"
#include "llvm/Support/raw_ostream.h"
#include <cctype>
#include <map>
#include <set>

using namespace clang;
using namespace verify;

// Emission budget guarding against exponential blow-up: VCExprs are DAGs with
// shared sub-terms (heap store/select chains in particular), and printing them
// as a tree re-expands shared nodes. The budget caps total emitted nodes so the
// Lean scratch-pad export always terminates.
static unsigned LeanEmitBudget = 0;
static bool LeanEmissionFailed = false;

static void printLeanName(const std::string &Name, llvm::raw_ostream &OS) {
  for (char C : Name)
    OS << (std::isalnum(static_cast<unsigned char>(C)) || C == '_' ? C : '_');
}

static void printLeanSort(const LogicSort &Sort, llvm::raw_ostream &OS) {
  switch (Sort.Kind) {
  case LogicSortKind::Bool:
    OS << "Prop";
    return;
  case LogicSortKind::MathematicalInteger:
  case LogicSortKind::Pointer:
    OS << "Int";
    return;
  case LogicSortKind::BitVector:
    OS << "BitVec " << Sort.BitWidth;
    return;
  case LogicSortKind::Heap:
    OS << "Array Int Int";
    return;
  case LogicSortKind::Invalid:
    LeanEmissionFailed = true;
    OS << "False";
    return;
  }
}

static void collectLeanVariables(const LogicExpr *E,
                                 std::set<std::string> Bound,
                                 std::map<std::string, LogicSort> &Variables) {
  if (!E) {
    LeanEmissionFailed = true;
    return;
  }
  if (E->K == VCExpr::Var && !Bound.count(E->Name)) {
    auto [It, Inserted] = Variables.emplace(E->Name, E->Sort);
    if (!Inserted && (It->second.Kind != E->Sort.Kind ||
                      It->second.BitWidth != E->Sort.BitWidth))
      LeanEmissionFailed = true;
  }
  if (E->K == VCExpr::Forall || E->K == VCExpr::Exists)
    Bound.insert(E->Binder);
  for (const auto &Child : E->Children)
    collectLeanVariables(Child.get(), Bound, Variables);
}

static void printVCExprLean(const VCExpr *E, llvm::raw_ostream &OS,
                            unsigned Prec = 0) {
  if (!E) {
    LeanEmissionFailed = true;
    OS << "False";
    return;
  }
  if (LeanEmitBudget == 0) {
    LeanEmissionFailed = true;
    return;
  }
  if (--LeanEmitBudget == 0) {
    LeanEmissionFailed = true;
    OS << "/- … expression elided (too large for the Lean scratch-pad) -/";
    return;
  }
  auto paren = [&](unsigned P, auto Fn) {
    if (Prec > P)
      OS << "(";
    Fn();
    if (Prec > P)
      OS << ")";
  };
  switch (E->K) {
  case VCExpr::True:
    OS << "True";
    break;
  case VCExpr::False:
    OS << "False";
    break;
  case VCExpr::BoolLit:
    OS << (E->BoolVal ? "True" : "False");
    break;
  case VCExpr::IntLit:
    OS << E->IntVal;
    break;
  case VCExpr::Var:
    printLeanName(E->Name, OS);
    break;
  case VCExpr::Not:
    OS << "¬";
    printVCExprLean(E->Children[0].get(), OS, 10);
    break;
  case VCExpr::And:
    paren(3, [&] {
      for (unsigned I = 0; I < E->Children.size(); ++I) {
        if (I)
          OS << " ∧ ";
        printVCExprLean(E->Children[I].get(), OS, 3);
      }
    });
    break;
  case VCExpr::Or:
    paren(2, [&] {
      for (unsigned I = 0; I < E->Children.size(); ++I) {
        if (I)
          OS << " ∨ ";
        printVCExprLean(E->Children[I].get(), OS, 2);
      }
    });
    break;
  case VCExpr::Ite:
    paren(1, [&] {
      OS << "if ";
      printVCExprLean(E->Children[0].get(), OS, 0);
      OS << " then ";
      printVCExprLean(E->Children[1].get(), OS, 0);
      OS << " else ";
      printVCExprLean(E->Children[2].get(), OS, 0);
    });
    break;
  case VCExpr::Eq:
    paren(5, [&] {
      printVCExprLean(E->Children[0].get(), OS, 5);
      OS << " = ";
      printVCExprLean(E->Children[1].get(), OS, 5);
    });
    break;
  case VCExpr::Ne:
    paren(5, [&] {
      printVCExprLean(E->Children[0].get(), OS, 5);
      OS << " ≠ ";
      printVCExprLean(E->Children[1].get(), OS, 5);
    });
    break;
  case VCExpr::Lt:
    paren(6, [&] {
      printVCExprLean(E->Children[0].get(), OS, 6);
      OS << " < ";
      printVCExprLean(E->Children[1].get(), OS, 6);
    });
    break;
  case VCExpr::Le:
    paren(6, [&] {
      printVCExprLean(E->Children[0].get(), OS, 6);
      OS << " ≤ ";
      printVCExprLean(E->Children[1].get(), OS, 6);
    });
    break;
  case VCExpr::Gt:
    paren(6, [&] {
      printVCExprLean(E->Children[0].get(), OS, 6);
      OS << " > ";
      printVCExprLean(E->Children[1].get(), OS, 6);
    });
    break;
  case VCExpr::Ge:
    paren(6, [&] {
      printVCExprLean(E->Children[0].get(), OS, 6);
      OS << " ≥ ";
      printVCExprLean(E->Children[1].get(), OS, 6);
    });
    break;
  case VCExpr::Add:
    paren(7, [&] {
      printVCExprLean(E->Children[0].get(), OS, 7);
      OS << " + ";
      printVCExprLean(E->Children[1].get(), OS, 7);
    });
    break;
  case VCExpr::Sub:
    paren(7, [&] {
      printVCExprLean(E->Children[0].get(), OS, 7);
      OS << " - ";
      printVCExprLean(E->Children[1].get(), OS, 7);
    });
    break;
  case VCExpr::Mul:
    paren(8, [&] {
      printVCExprLean(E->Children[0].get(), OS, 8);
      OS << " * ";
      printVCExprLean(E->Children[1].get(), OS, 8);
    });
    break;
  case VCExpr::Div:
    paren(8, [&] {
      printVCExprLean(E->Children[0].get(), OS, 8);
      OS << " / ";
      printVCExprLean(E->Children[1].get(), OS, 8);
    });
    break;
  case VCExpr::Rem:
    paren(8, [&] {
      printVCExprLean(E->Children[0].get(), OS, 8);
      OS << " % ";
      printVCExprLean(E->Children[1].get(), OS, 8);
    });
    break;
  case VCExpr::BitAnd:
  case VCExpr::BitOr:
  case VCExpr::BitXor:
  case VCExpr::Shl:
  case VCExpr::Shr: {
    const char *Name = E->K == VCExpr::BitAnd   ? "Int.and"
                       : E->K == VCExpr::BitOr  ? "Int.or"
                       : E->K == VCExpr::BitXor ? "Int.xor"
                       : E->K == VCExpr::Shl    ? "Int.shiftLeft"
                                                : "Int.shiftRight";
    OS << Name << " ";
    printVCExprLean(E->Children[0].get(), OS, 9);
    OS << " ";
    printVCExprLean(E->Children[1].get(), OS, 9);
    break;
  }
  case VCExpr::Neg:
    OS << "-";
    printVCExprLean(E->Children[0].get(), OS, 9);
    break;
  case VCExpr::BitNot:
    OS << "Int.not ";
    printVCExprLean(E->Children[0].get(), OS, 9);
    break;
  case VCExpr::ValidPtr:
    OS << "validPtr ";
    printVCExprLean(E->Children[0].get(), OS, 9);
    break;
  case VCExpr::Select:
    OS << "heapSelect ";
    printVCExprLean(E->Children[0].get(), OS, 0);
    OS << " ";
    printVCExprLean(E->Children[1].get(), OS, 0);
    break;
  case VCExpr::Store:
    OS << "heapStore ";
    printVCExprLean(E->Children[0].get(), OS, 0);
    OS << " ";
    printVCExprLean(E->Children[1].get(), OS, 0);
    OS << " ";
    printVCExprLean(E->Children[2].get(), OS, 0);
    OS << " ";
    printVCExprLean(E->Children[3].get(), OS, 0);
    break;
  case VCExpr::Forall:
  case VCExpr::Exists:
    OS << (E->K == VCExpr::Forall ? "∀ (" : "∃ (");
    printLeanName(E->Binder, OS);
    OS << " : Int), ";
    printVCExprLean(E->Children[0].get(), OS, 6);
    OS << " ≤ ";
    printLeanName(E->Binder, OS);
    OS << " ∧ ";
    printLeanName(E->Binder, OS);
    OS << " < ";
    printVCExprLean(E->Children[1].get(), OS, 6);
    OS << (E->K == VCExpr::Forall ? " → " : " ∧ ");
    printVCExprLean(E->Children[2].get(), OS, 2);
    break;
  case VCExpr::IntToBv:
  case VCExpr::BvToInt:
  case VCExpr::BvResize:
    printVCExprLean(E->Children[0].get(), OS, Prec);
    break;
  case VCExpr::NoOverflow:
    OS << (E->Children.size() == 1 ? "noOverflowUnary " : "noOverflowBinary ");
    for (const auto &Child : E->Children) {
      printVCExprLean(Child.get(), OS, 9);
      OS << " ";
    }
    break;
  case VCExpr::SpecCall:
    printLeanName(E->SpecCallee, OS);
    for (const auto &Arg : E->Children) {
      OS << " ";
      printVCExprLean(Arg.get(), OS, 9);
    }
    break;
  }
}

VerifyResult verify::exportLeanScratchPad(const ObligationModule &Module,
                                          llvm::raw_ostream &OS,
                                          bool EmitPreamble) {
  VerifyResult Result;
  if (!Module.CounterexampleQuery) {
    Result.Status = VerifyStatus::Unknown;
    Result.Message = "missing counterexample query for Lean export";
    return Result;
  }

  LeanEmissionFailed = false;
  std::map<std::string, LogicSort> Variables;
  collectLeanVariables(Module.CounterexampleQuery.get(), {}, Variables);

  if (EmitPreamble) {
    OS << "/- Generated by CppVerify (unchecked Lean scratch-pad).\n";
    OS << "   This file exports canonical obligations but does not certify "
          "them. "
          "-/\n\n";
    OS << "def heapSelect (h : Array Int Int) (p : Int) : Int := h[p]!\n";
    OS << "def heapStore (h : Array Int Int) (p : Int) (v : Int) (h' : "
          "Array Int Int) : Prop :=\n";
    OS << "  h' = h.set! p v\n\n";
    OS << "opaque validPtr : Int -> Prop\n\n";
    OS << "opaque noOverflowUnary : Int -> Prop\n";
    OS << "opaque noOverflowBinary : Int -> Int -> Prop\n\n";
  }

  OS << "/- function: " << Module.FunctionName << " -/\n";
  OS << "/- required logic: " << formatLogicFeatures(Module.RequiredFeatures)
     << " -/\n\n";

  OS << "theorem cppverify_";
  printLeanName(Module.FunctionName.empty() ? "goal" : Module.FunctionName, OS);
  if (!Module.FunctionIdentity.empty()) {
    OS << "_";
    printLeanName(Module.FunctionIdentity, OS);
  }
  OS << "_correct";
  for (const auto &[Name, Sort] : Variables) {
    OS << "\n    (";
    printLeanName(Name, OS);
    OS << " : ";
    printLeanSort(Sort, OS);
    OS << ")";
  }
  OS << " : ¬ (";
  LeanEmitBudget = 500000;
  printVCExprLean(Module.CounterexampleQuery.get(), OS);
  OS << ") := by\n  sorry\n\n";

  if (LeanEmissionFailed) {
    Result.Status = VerifyStatus::Unknown;
    Result.Message = "Lean export exceeded its budget or contained an invalid "
                     "logical term";
    return Result;
  }
  Result.Status = VerifyStatus::Exported;
  Result.Message = "unchecked Lean obligation export";
  return Result;
}