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
static thread_local unsigned LeanEmitBudget = 0;
static thread_local bool LeanEmissionFailed = false;
static thread_local const std::map<std::string, LogicFunctionDecl>
    *LeanLogicFunctions = nullptr;
static thread_local std::string LeanBodyPrefix;
static thread_local std::map<const LogicExpr *, unsigned> LeanTemporaryNames;
static thread_local const LogicExpr *LeanTemporaryRoot = nullptr;
static thread_local const LogicFunctionDecl *LeanActiveDefinition = nullptr;
static thread_local unsigned LeanActiveDefinitionDepth = 0;

static bool needsLeanNameEncoding(llvm::StringRef Name) {
  static const std::set<llvm::StringRef> Keywords = {
      "abbrev",     "axiom",     "by",        "class",         "def",
      "deriving",   "do",        "else",      "end",           "example",
      "export",     "extends",   "for",       "forall",        "fun",
      "if",         "import",    "in",        "inductive",     "infix",
      "infixl",     "infixr",    "instance",  "let",           "macro",
      "match",      "mutual",    "namespace", "noncomputable", "opaque",
      "open",       "partial",   "postfix",   "precedence",    "prefix",
      "private",    "protected", "public",    "return",        "section",
      "set_option", "structure", "syntax",    "then",          "theorem",
      "universe",   "variable",  "where",     "with"};
  if (Name.empty() || Name == "_" || Name.starts_with("cppEncoded_") ||
      Keywords.count(Name))
    return true;
  if (!std::isalpha(static_cast<unsigned char>(Name.front())) &&
      Name.front() != '_')
    return true;
  for (char C : Name)
    if (!std::isalnum(static_cast<unsigned char>(C)) && C != '_')
      return true;
  return false;
}

static std::string encodeLeanName(llvm::StringRef Name) {
  if (!needsLeanNameEncoding(Name))
    return Name.str();

  static constexpr char Hex[] = "0123456789abcdef";
  std::string Encoded = "cppEncoded_";
  Encoded.reserve(Encoded.size() + 2 * Name.size());
  for (unsigned char C : Name)
    Encoded.append({Hex[C >> 4], Hex[C & 0xf]});
  return Encoded;
}

static void printLeanName(llvm::StringRef Name, llvm::raw_ostream &OS) {
  OS << encodeLeanName(Name);
}

static void printLeanCommentText(llvm::StringRef Text, llvm::raw_ostream &OS) {
  for (size_t I = 0; I < Text.size(); ++I) {
    if (Text[I] == '\n' || Text[I] == '\r') {
      OS << " ";
      continue;
    }
    if (I + 1 < Text.size() && ((Text[I] == '-' && Text[I + 1] == '/') ||
                                (Text[I] == '/' && Text[I + 1] == '-'))) {
      OS << Text[I] << " " << Text[I + 1];
      ++I;
      continue;
    }
    OS << Text[I];
  }
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
    OS << "CppHeap";
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
                      It->second.BitWidth != E->Sort.BitWidth ||
                      It->second.Signedness != E->Sort.Signedness))
      LeanEmissionFailed = true;
  }
  if (E->K == VCExpr::Forall || E->K == VCExpr::Exists)
    Bound.insert(E->Binder);
  for (const auto &Child : E->Children)
    collectLeanVariables(Child.get(), Bound, Variables);
}

static bool sameLeanSort(const LogicSort &Left, const LogicSort &Right) {
  if (Left.Kind != Right.Kind)
    return false;
  if (Left.Kind == LogicSortKind::MathematicalInteger)
    return true;
  return Left.BitWidth == Right.BitWidth && Left.Signedness == Right.Signedness;
}

static void printVCExprLean(const VCExpr *E, llvm::raw_ostream &OS,
                            unsigned Prec);

static void printLeanCoerced(const LogicExpr *Expression,
                             const LogicSort &Target, bool IsSigned,
                             llvm::raw_ostream &OS) {
  if (sameLeanSort(Expression->Sort, Target)) {
    printVCExprLean(Expression, OS, 10);
    return;
  }
  if (Target.Kind == LogicSortKind::BitVector &&
      (Expression->Sort.Kind == LogicSortKind::MathematicalInteger ||
       Expression->Sort.Kind == LogicSortKind::Pointer)) {
    OS << "(BitVec.ofInt " << Target.BitWidth << " (";
    printVCExprLean(Expression, OS, 0);
    OS << "))";
    return;
  }
  if ((Target.Kind == LogicSortKind::MathematicalInteger ||
       Target.Kind == LogicSortKind::Pointer) &&
      Expression->Sort.Kind == LogicSortKind::BitVector) {
    if (IsSigned) {
      OS << "(";
      printVCExprLean(Expression, OS, 0);
      OS << ").toInt";
    } else {
      OS << "(Int.ofNat (";
      printVCExprLean(Expression, OS, 0);
      OS << ").toNat)";
    }
    return;
  }
  LeanEmissionFailed = true;
  printVCExprLean(Expression, OS, 10);
}

static void printLeanSpecName(llvm::StringRef Identity, llvm::raw_ostream &OS) {
  OS << "cppSpec_";
  printLeanName(Identity.str(), OS);
}

static void printLeanBodyName(const LogicFunctionDecl &Function, unsigned Level,
                              llvm::raw_ostream &OS) {
  OS << LeanBodyPrefix;
  printLeanName(Function.Identity, OS);
  OS << "_" << Level + 1;
}

static const LogicFunctionDecl *findLeanFunction(llvm::StringRef Identity) {
  if (!LeanLogicFunctions)
    return nullptr;
  auto It = LeanLogicFunctions->find(Identity.str());
  return It == LeanLogicFunctions->end() ? nullptr : &It->second;
}

static void printLeanNativeSpecCall(const LogicExpr *Call,
                                    const LogicFunctionDecl &Function,
                                    llvm::raw_ostream &OS) {
  OS << "(";
  if (LeanActiveDefinition == &Function && LeanActiveDefinitionDepth > 1)
    printLeanBodyName(Function, LeanActiveDefinitionDepth - 2, OS);
  else
    printLeanSpecName(Function.Identity, OS);
  for (unsigned I = 0; I < Call->Children.size(); ++I) {
    OS << " ";
    printLeanCoerced(
        Call->Children[I].get(), Function.Parameters[I].Sort,
        Function.Parameters[I].Sort.Signedness == LogicSignedness::Signed, OS);
  }
  OS << ")";
}

static void printVCExprLean(const VCExpr *E, llvm::raw_ostream &OS,
                            unsigned Prec) {
  if (!E) {
    LeanEmissionFailed = true;
    OS << "False";
    return;
  }
  if (E != LeanTemporaryRoot) {
    if (auto It = LeanTemporaryNames.find(E); It != LeanTemporaryNames.end()) {
      OS << "__cppverify_term_" << It->second;
      return;
    }
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
    if (E->Sort.Kind == LogicSortKind::BitVector)
      OS << "(BitVec.ofInt " << E->Sort.BitWidth << " (" << E->IntVal << "))";
    else
      OS << "(" << E->IntVal << ")";
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
  case VCExpr::Le:
  case VCExpr::Gt:
  case VCExpr::Ge:
    if (E->Children[0]->Sort.Kind == LogicSortKind::BitVector) {
      const bool Reverse = E->K == VCExpr::Gt || E->K == VCExpr::Ge;
      const bool Inclusive = E->K == VCExpr::Le || E->K == VCExpr::Ge;
      OS << "("
         << (E->Children[0]->Sort.Signedness == LogicSignedness::Signed
                 ? "cppBvS"
                 : "cppBvU")
         << (Inclusive ? "le " : "lt ");
      printVCExprLean(E->Children[Reverse ? 1 : 0].get(), OS, 10);
      OS << " ";
      printVCExprLean(E->Children[Reverse ? 0 : 1].get(), OS, 10);
      OS << ")";
      break;
    }
    paren(6, [&] {
      printVCExprLean(E->Children[0].get(), OS, 6);
      OS << (E->K == VCExpr::Lt   ? " < "
             : E->K == VCExpr::Le ? " ≤ "
             : E->K == VCExpr::Gt ? " > "
                                  : " ≥ ");
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
    OS << "("
       << (E->Sort.Kind == LogicSortKind::BitVector
               ? (E->Sort.Signedness == LogicSignedness::Signed
                      ? "BitVec.sdiv "
                      : "BitVec.udiv ")
               : "cppIntDiv ");
    printVCExprLean(E->Children[0].get(), OS, 9);
    OS << " ";
    printVCExprLean(E->Children[1].get(), OS, 9);
    OS << ")";
    break;
  case VCExpr::Rem:
    OS << "("
       << (E->Sort.Kind == LogicSortKind::BitVector
               ? (E->Sort.Signedness == LogicSignedness::Signed
                      ? "BitVec.srem "
                      : "BitVec.umod ")
               : "cppIntRem ");
    printVCExprLean(E->Children[0].get(), OS, 9);
    OS << " ";
    printVCExprLean(E->Children[1].get(), OS, 9);
    OS << ")";
    break;
  case VCExpr::BitAnd:
  case VCExpr::BitOr:
  case VCExpr::BitXor: {
    paren(7, [&] {
      printVCExprLean(E->Children[0].get(), OS, 7);
      OS << (E->K == VCExpr::BitAnd  ? " &&& "
             : E->K == VCExpr::BitOr ? " ||| "
                                     : " ^^^ ");
      printVCExprLean(E->Children[1].get(), OS, 7);
    });
    break;
  }
  case VCExpr::Shl:
    paren(7, [&] {
      printVCExprLean(E->Children[0].get(), OS, 7);
      OS << " <<< ";
      printVCExprLean(E->Children[1].get(), OS, 7);
    });
    break;
  case VCExpr::Shr:
    if (E->Sort.Signedness == LogicSignedness::Signed) {
      OS << "BitVec.sshiftRight ";
      printVCExprLean(E->Children[0].get(), OS, 9);
      OS << " (";
      printVCExprLean(E->Children[1].get(), OS, 0);
      OS << ").toNat";
    } else {
      paren(7, [&] {
        printVCExprLean(E->Children[0].get(), OS, 7);
        OS << " >>> ";
        printVCExprLean(E->Children[1].get(), OS, 7);
      });
    }
    break;
  case VCExpr::Neg:
    OS << "-";
    printVCExprLean(E->Children[0].get(), OS, 9);
    break;
  case VCExpr::BitNot:
    OS << "~~~";
    printVCExprLean(E->Children[0].get(), OS, 9);
    break;
  case VCExpr::ValidPtr:
    OS << "(validPtr ";
    printVCExprLean(E->Children[0].get(), OS, 10);
    OS << ")";
    break;
  case VCExpr::Select:
    OS << "(";
    if (E->Sort.Kind == LogicSortKind::Bool)
      OS << "heapSelectBool ";
    else if (E->Sort.Kind == LogicSortKind::BitVector)
      OS << "heapSelectBv " << E->Sort.BitWidth << " ";
    else
      OS << "heapSelectInt ";
    printVCExprLean(E->Children[0].get(), OS, 10);
    OS << " ";
    printVCExprLean(E->Children[1].get(), OS, 10);
    OS << ")";
    break;
  case VCExpr::Store:
    OS << "(";
    if (E->Children[2]->Sort.Kind == LogicSortKind::Bool)
      OS << "heapStoreBool ";
    else if (E->Children[2]->Sort.Kind == LogicSortKind::BitVector)
      OS << "heapStoreBv ";
    else
      OS << "heapStoreInt ";
    printVCExprLean(E->Children[0].get(), OS, 10);
    OS << " ";
    printVCExprLean(E->Children[1].get(), OS, 10);
    OS << " ";
    printVCExprLean(E->Children[2].get(), OS, 10);
    OS << " ";
    printVCExprLean(E->Children[3].get(), OS, 10);
    OS << ")";
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
    OS << "(BitVec.ofInt " << E->Sort.BitWidth << " (";
    printVCExprLean(E->Children[0].get(), OS, 0);
    OS << "))";
    break;
  case VCExpr::BvToInt:
    if (E->Children[0]->Sort.Signedness == LogicSignedness::Signed) {
      OS << "(";
      printVCExprLean(E->Children[0].get(), OS, 0);
      OS << ").toInt";
    } else {
      OS << "(Int.ofNat (";
      printVCExprLean(E->Children[0].get(), OS, 0);
      OS << ").toNat)";
    }
    break;
  case VCExpr::BvResize:
    OS << "("
       << (E->Children[0]->Sort.Signedness == LogicSignedness::Signed
               ? "BitVec.signExtend "
               : "BitVec.zeroExtend ")
       << E->Sort.BitWidth << " ";
    printVCExprLean(E->Children[0].get(), OS, 10);
    OS << ")";
    break;
  case VCExpr::NoOverflow: {
    const unsigned BitWidth = E->Children[0]->Sort.BitWidth;
    const char *Check = E->OverflowOp == LogicOverflowOp::Add   ? "saddOverflow"
                        : E->OverflowOp == LogicOverflowOp::Sub ? "ssubOverflow"
                        : E->OverflowOp == LogicOverflowOp::Mul ? "smulOverflow"
                        : E->OverflowOp == LogicOverflowOp::Neg
                            ? "negOverflow"
                            : "sdivOverflow";
    OS << "(BitVec." << Check << " ";
    for (unsigned I = 0; I < E->Children.size(); ++I) {
      if (I)
        OS << " ";
      OS << "("
         << (E->Children[I]->Sort.Signedness == LogicSignedness::Signed
                 ? "BitVec.signExtend "
                 : "BitVec.zeroExtend ")
         << BitWidth << " ";
      printVCExprLean(E->Children[I].get(), OS, 10);
      OS << ")";
    }
    OS << " = false)";
    break;
  }
  case VCExpr::SpecCall:
    if (const LogicFunctionDecl *Function = findLeanFunction(E->SpecCallee)) {
      if (E->Children.size() != Function->Parameters.size()) {
        LeanEmissionFailed = true;
        OS << "False";
        break;
      }
      const bool SameResult = sameLeanSort(Function->ResultSort, E->Sort);
      if (!SameResult &&
          (E->Sort.Kind == LogicSortKind::MathematicalInteger ||
           E->Sort.Kind == LogicSortKind::Pointer) &&
          Function->ResultSort.Kind == LogicSortKind::BitVector) {
        if (Function->ResultSort.Signedness == LogicSignedness::Signed) {
          OS << "(";
          printLeanNativeSpecCall(E, *Function, OS);
          OS << ").toInt";
        } else {
          OS << "(Int.ofNat (";
          printLeanNativeSpecCall(E, *Function, OS);
          OS << ").toNat)";
        }
      } else if (!SameResult && E->Sort.Kind == LogicSortKind::BitVector &&
                 (Function->ResultSort.Kind ==
                      LogicSortKind::MathematicalInteger ||
                  Function->ResultSort.Kind == LogicSortKind::Pointer)) {
        OS << "(BitVec.ofInt " << E->Sort.BitWidth << " (";
        printLeanNativeSpecCall(E, *Function, OS);
        OS << "))";
      } else if (SameResult) {
        printLeanNativeSpecCall(E, *Function, OS);
      } else {
        LeanEmissionFailed = true;
        OS << "False";
      }
    } else {
      LeanEmissionFailed = true;
      OS << "False";
    }
    break;
  }
}

static unsigned collectLeanTemporaries(const LogicExpr *Expression,
                                       std::vector<const LogicExpr *> &Nodes,
                                       bool IsRoot = false) {
  if (!Expression || Expression->Children.empty())
    return 1;
  unsigned Size = 1;
  if (Expression->K != LogicExpr::Forall && Expression->K != LogicExpr::Exists)
    for (const auto &Child : Expression->Children)
      Size += collectLeanTemporaries(Child.get(), Nodes);
  if (!IsRoot && Size >= 128) {
    Nodes.push_back(Expression);
    return 1;
  }
  return Size;
}

static void printLeanFlattened(const LogicExpr *Expression,
                               llvm::raw_ostream &OS) {
  LeanTemporaryNames.clear();
  LeanTemporaryRoot = nullptr;
  std::vector<const LogicExpr *> Nodes;
  collectLeanTemporaries(Expression, Nodes, true);
  if (Nodes.empty()) {
    printVCExprLean(Expression, OS, 0);
    return;
  }

  unsigned Index = 0;
  for (const LogicExpr *Node : Nodes)
    LeanTemporaryNames.emplace(Node, ++Index);

  OS << "(let ";
  for (const LogicExpr *Node : Nodes) {
    const unsigned Name = LeanTemporaryNames.at(Node);
    if (Name > 1)
      OS << "let ";
    OS << "__cppverify_term_" << Name << " : ";
    printLeanSort(Node->Sort, OS);
    OS << " := ";
    LeanTemporaryRoot = Node;
    printVCExprLean(Node, OS, 0);
    OS << ";\n  ";
  }
  LeanTemporaryRoot = nullptr;
  printVCExprLean(Expression, OS, 0);
  OS << ")";
  LeanTemporaryNames.clear();
}

static const char *leanObligationKind(ObligationKind Kind) {
  switch (Kind) {
  case ObligationKind::Assertion:
    return "assertion";
  case ObligationKind::Postcondition:
    return "postcondition";
  case ObligationKind::Unwinding:
    return "unwinding";
  }
  return "assertion";
}

static void collectLeanSpecCalls(const LogicExpr *Expression,
                                 std::vector<const LogicExpr *> &Calls) {
  if (!Expression)
    return;
  if (Expression->K == LogicExpr::SpecCall)
    Calls.push_back(Expression);
  for (const auto &Child : Expression->Children)
    collectLeanSpecCalls(Child.get(), Calls);
}

static unsigned emitLeanSpecAxiomBinders(const LogicExpr *Goal,
                                         llvm::raw_ostream &OS) {
  std::vector<const LogicExpr *> Calls;
  collectLeanSpecCalls(Goal, Calls);
  unsigned CallIndex = 0;
  unsigned BinderCount = 0;
  for (const LogicExpr *Call : Calls) {
    const LogicFunctionDecl *Function = findLeanFunction(Call->SpecCallee);
    if (!Function || Call->Children.size() != Function->Parameters.size()) {
      LeanEmissionFailed = true;
      continue;
    }
    ++CallIndex;
    for (unsigned Level = 0; Level < Function->DefinitionFuel; ++Level) {
      ++BinderCount;
      OS << "\n    (cppverify_spec_axiom_" << CallIndex << "_" << Level + 1
         << " : ";
      printLeanNativeSpecCall(Call, *Function, OS);
      OS << " = (";
      for (unsigned I = 0; I < Function->Parameters.size(); ++I) {
        if (I == 0)
          printLeanBodyName(*Function, Level, OS);
        OS << " ";
        printLeanCoerced(Call->Children[I].get(), Function->Parameters[I].Sort,
                         Function->Parameters[I].Sort.Signedness ==
                             LogicSignedness::Signed,
                         OS);
      }
      if (Function->Parameters.empty())
        printLeanBodyName(*Function, Level, OS);
      OS << "))";
    }
  }
  return BinderCount;
}

static void
emitLeanVariableBinders(const std::map<std::string, LogicSort> &Variables,
                        llvm::raw_ostream &OS) {
  for (const auto &[Variable, Sort] : Variables) {
    OS << "\n    (";
    printLeanName(Variable, OS);
    OS << " : ";
    printLeanSort(Sort, OS);
    OS << ")";
  }
}

static void emitLeanTheorem(llvm::StringRef Name, const LogicExpr *Goal,
                            llvm::raw_ostream &OS) {
  LeanEmitBudget = 500000;
  std::map<std::string, LogicSort> Variables;
  collectLeanVariables(Goal, {}, Variables);
  OS << "theorem ";
  printLeanName(Name.str(), OS);
  emitLeanVariableBinders(Variables, OS);
  emitLeanSpecAxiomBinders(Goal, OS);
  OS << " : ";
  printLeanFlattened(Goal, OS);
  OS << " := by\n  sorry\n\n";
}

static void emitLeanGoalDefinition(llvm::StringRef Name, const LogicExpr *Goal,
                                   llvm::raw_ostream &OS) {
  LeanEmitBudget = 500000;
  std::map<std::string, LogicSort> Variables;
  collectLeanVariables(Goal, {}, Variables);
  std::vector<const LogicExpr *> Calls;
  collectLeanSpecCalls(Goal, Calls);
  bool HasSpecAxioms = false;
  for (const LogicExpr *Call : Calls)
    if (const LogicFunctionDecl *Function = findLeanFunction(Call->SpecCallee);
        Function && Function->DefinitionFuel > 0) {
      HasSpecAxioms = true;
      break;
    }

  OS << "def ";
  printLeanName(Name.str(), OS);
  OS << " : Prop :=\n  ";
  if (!Variables.empty() || HasSpecAxioms) {
    OS << "∀";
    emitLeanVariableBinders(Variables, OS);
    emitLeanSpecAxiomBinders(Goal, OS);
    OS << ",\n    ";
  }
  printLeanFlattened(Goal, OS);
  OS << "\n\n";
}

static void
emitLeanFunctionDeclarations(const ObligationModule &Module,
                             llvm::raw_ostream &OS,
                             std::set<std::string> &EmittedFunctions) {
  for (const auto &[Identity, Function] : Module.LogicFunctions) {
    if (!EmittedFunctions.insert(Identity).second)
      continue;
    OS << "/- spec function: ";
    printLeanCommentText(Function.DisplayName, OS);
    OS << " -/\n";
    OS << "opaque ";
    printLeanSpecName(Identity, OS);
    OS << " : ";
    for (const LogicFunctionParameter &Parameter : Function.Parameters) {
      printLeanSort(Parameter.Sort, OS);
      OS << " -> ";
    }
    printLeanSort(Function.ResultSort, OS);
    OS << "\n\n";
  }
}

static void emitLeanFunctionBodies(const ObligationModule &Module,
                                   llvm::raw_ostream &OS) {
  for (const auto &[Identity, Function] : Module.LogicFunctions) {
    (void)Identity;
    if (Function.DefinitionFuel > 0 && !Function.StepDefinition) {
      LeanEmissionFailed = true;
      continue;
    }
    for (unsigned Level = 0; Level < Function.DefinitionFuel; ++Level) {
      LeanEmitBudget = 1000000;
      OS << "def ";
      printLeanBodyName(Function, Level, OS);
      for (const LogicFunctionParameter &Parameter : Function.Parameters) {
        OS << "\n    (";
        printLeanName(Parameter.Name, OS);
        OS << " : ";
        printLeanSort(Parameter.Sort, OS);
        OS << ")";
      }
      OS << " : ";
      printLeanSort(Function.ResultSort, OS);
      OS << " :=\n  ";
      LeanActiveDefinition = &Function;
      LeanActiveDefinitionDepth = Level + 1;
      printLeanFlattened(Function.StepDefinition.get(), OS);
      LeanActiveDefinition = nullptr;
      LeanActiveDefinitionDepth = 0;
      OS << "\n\n";
    }
  }
}

VerifyResult verify::exportLeanScratchPad(
    const ObligationModule &Module, llvm::raw_ostream &OS, bool EmitPreamble,
    std::set<std::string> &EmittedFunctions,
    std::set<std::string> &EmittedTheorems, unsigned ModuleIndex,
    std::vector<std::string> *ProjectGoals) {
  VerifyResult Result;
  if (!Module.CorrectnessGoal || !Module.CounterexampleQuery) {
    Result.Status = VerifyStatus::Unresolved;
    Result.Message = "missing correctness goal for Lean export";
    return Result;
  }

  LeanEmissionFailed = false;
  LeanLogicFunctions = &Module.LogicFunctions;
  LeanBodyPrefix = "cppSpecBody_m" + std::to_string(ModuleIndex) + "_";

  if (EmitPreamble) {
    if (ProjectGoals) {
      OS << "/- Generated by CppVerify for an editable Lean project.\n";
      OS << "   Regeneration replaces this file, never user proofs. -/\n\n";
    } else {
      OS << "/- Generated by CppVerify (unchecked Lean scratch-pad).\n";
      OS << "   This file exports canonical obligations but does not certify "
            "them. -/\n\n";
    }
    OS << "noncomputable section\n\n";
    OS << "set_option maxRecDepth 100000\n";
    OS << "set_option maxHeartbeats 0\n\n";
    OS << "local instance cppVerifyPropDecidable (p : Prop) : Decidable p :=\n";
    OS << "  Classical.propDecidable p\n\n";
    OS << "abbrev CppHeap := Int -> Int\n\n";
    OS << "def heapSelectInt (h : CppHeap) (p : Int) : Int := h p\n";
    OS << "def heapSelectBool (h : CppHeap) (p : Int) : Prop := h p ≠ 0\n";
    OS << "def heapSelectBv (w : Nat) (h : CppHeap) (p : Int) : BitVec w :=\n";
    OS << "  BitVec.ofInt w (h p)\n\n";
    OS << "def heapStoreInt (h : CppHeap) (p v : Int) (h' : CppHeap) : "
          "Prop :=\n";
    OS << "  h' = fun q => if q = p then v else h q\n";
    OS << "def heapStoreBool (h : CppHeap) (p : Int) (v : Prop)\n";
    OS << "    (h' : CppHeap) : Prop :=\n";
    OS << "  h' = fun q => if q = p then\n";
    OS << "    @ite Int v (Classical.propDecidable v) 1 0 else h q\n";
    OS << "def heapStoreBv {w : Nat} (h : CppHeap) (p : Int) (v : BitVec w)\n";
    OS << "    (h' : CppHeap) : Prop :=\n";
    OS << "  h' = fun q => if q = p then Int.ofNat v.toNat else h q\n\n";
    OS << "opaque validPtr : Int -> Prop\n\n";
    OS << "def cppBvUlt {w : Nat} (x y : BitVec w) : Prop := x.ult y = true\n";
    OS << "def cppBvUle {w : Nat} (x y : BitVec w) : Prop := x.ule y = true\n";
    OS << "def cppBvSlt {w : Nat} (x y : BitVec w) : Prop := x.slt y = true\n";
    OS << "def cppBvSle {w : Nat} (x y : BitVec w) : Prop := x.sle y = "
          "true\n\n";
    OS << "def cppIntDiv (x y : Int) : Int :=\n";
    OS << "  if y = 0 then 0 else\n";
    OS << "    let q := (if x < 0 then -x else x) / "
          "(if y < 0 then -y else y)\n";
    OS << "    if (x < 0) ≠ (y < 0) then -q else q\n";
    OS << "def cppIntRem (x y : Int) : Int :=\n";
    OS << "  if y = 0 then x else x - cppIntDiv x y * y\n\n";
  }

  emitLeanFunctionDeclarations(Module, OS, EmittedFunctions);
  emitLeanFunctionBodies(Module, OS);
  OS << "/- function: ";
  printLeanCommentText(Module.FunctionName, OS);
  OS << " -/\n";
  OS << "/- required logic: " << formatLogicFeatures(Module.RequiredFeatures)
     << " -/\n\n";

  std::string TheoremName =
      "cppverify_" +
      (Module.FunctionName.empty() ? std::string("goal") : Module.FunctionName);
  if (!Module.FunctionIdentity.empty()) {
    TheoremName += "_" + Module.FunctionIdentity;
  }
  if (!EmittedTheorems.insert(TheoremName).second) {
    const std::string BaseName = TheoremName;
    unsigned Suffix = ModuleIndex;
    do {
      TheoremName = BaseName + "_module_" + std::to_string(Suffix++);
    } while (!EmittedTheorems.insert(TheoremName).second);
  }
  if (!ProjectGoals)
    emitLeanTheorem(TheoremName + "_correct", Module.CorrectnessGoal.get(), OS);

  unsigned Index = 0;
  for (const Obligation &Item : Module.Obligations) {
    OS << "/- obligation: ";
    printLeanCommentText(Item.Id, OS);
    OS << "\n";
    OS << "   kind: " << leanObligationKind(Item.Kind) << "\n";
    OS << "   source: ";
    if (Item.Source.isValid()) {
      printLeanCommentText(Item.Source.File, OS);
      OS << ":" << Item.Source.Line << ":" << Item.Source.Column;
    } else if (Item.Loc.isValid()) {
      OS << Item.Loc.getRawEncoding();
    } else {
      OS << "unknown";
    }
    OS << " -/\n";
    std::string ObligationName =
        TheoremName + "_obligation_" + std::to_string(++Index);
    if (ProjectGoals) {
      ObligationName += "_goal";
      emitLeanGoalDefinition(ObligationName, Item.Goal.get(), OS);
      ProjectGoals->push_back(encodeLeanName(ObligationName));
    } else {
      emitLeanTheorem(ObligationName, Item.Goal.get(), OS);
    }
  }

  if (LeanEmissionFailed) {
    LeanLogicFunctions = nullptr;
    LeanBodyPrefix.clear();
    Result.Status = VerifyStatus::Unresolved;
    Result.Message = "Lean export exceeded its budget or contained an invalid "
                     "logical term";
    return Result;
  }
  LeanLogicFunctions = nullptr;
  LeanBodyPrefix.clear();
  Result.Status = VerifyStatus::Exported;
  Result.Message = ProjectGoals ? "editable Lean project obligation export"
                                : "unchecked Lean obligation export";
  return Result;
}