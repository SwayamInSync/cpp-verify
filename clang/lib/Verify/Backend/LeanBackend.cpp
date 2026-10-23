//===--- LeanBackend.cpp --------------------------------------------------===//
#include "LeanBackend.h"
#include "ObligationSerialization.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/Support/MD5.h"
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

// The characters a Lean identifier takes; the others become `_`.
static std::string leanIdentifierPart(llvm::StringRef Text) {
  std::string Part;
  for (char C : Text)
    Part += std::isalnum(static_cast<unsigned char>(C)) ? C : '_';
  return Part;
}

static std::string leanShortHash(llvm::StringRef Text, unsigned Digits) {
  llvm::MD5 Hasher;
  llvm::MD5::MD5Result Hash;
  Hasher.update(Text);
  Hasher.final(Hash);
  llvm::SmallString<32> Hex;
  llvm::MD5::stringifyResult(Hash, Hex);
  return llvm::StringRef(Hex).take_front(Digits).str();
}

std::string verify::leanProjectGroup(const ObligationModule &Module) {
  return "cppverify_" +
         leanIdentifierPart(Module.FunctionName.empty()
                                ? llvm::StringRef("goal")
                                : llvm::StringRef(Module.FunctionName)) +
         "_" + leanShortHash(Module.FunctionIdentity, 6);
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
  case LogicSortKind::Seq:
  case LogicSortKind::Set:
  case LogicSortKind::Multiset:
  case LogicSortKind::Map:
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

// Lean 4's notation levels (Init/Notation.lean, Init/Core.lean). A context
// needs an operand of at least its level, and one that binds looser is
// parenthesized; a function argument needs an atom.
enum : unsigned {
  LeanTop = 0,
  LeanIff = 20,
  LeanArrow = 25,
  LeanOr = 30,
  LeanAnd = 35,
  LeanNot = 40,
  LeanCompare = 50,
  LeanBitOr = 55,
  LeanBitXor = 58,
  LeanBitAnd = 60,
  LeanAdd = 65,
  LeanMul = 70,
  LeanShift = 75,
  LeanArgument = 1024
};

static void printVCExprLean(const VCExpr *E, llvm::raw_ostream &OS,
                            unsigned Prec);

static void printLeanCoerced(const LogicExpr *Expression,
                             const LogicSort &Target, bool IsSigned,
                             llvm::raw_ostream &OS) {
  if (sameLeanSort(Expression->Sort, Target)) {
    printVCExprLean(Expression, OS, LeanArgument);
    return;
  }
  if (Target.Kind == LogicSortKind::BitVector &&
      (Expression->Sort.Kind == LogicSortKind::MathematicalInteger ||
       Expression->Sort.Kind == LogicSortKind::Pointer)) {
    OS << "(BitVec.ofInt " << Target.BitWidth << " (";
    printVCExprLean(Expression, OS, LeanTop);
    OS << "))";
    return;
  }
  if ((Target.Kind == LogicSortKind::MathematicalInteger ||
       Target.Kind == LogicSortKind::Pointer) &&
      Expression->Sort.Kind == LogicSortKind::BitVector) {
    if (IsSigned) {
      OS << "(";
      printVCExprLean(Expression, OS, LeanTop);
      OS << ").toInt";
    } else {
      OS << "(Int.ofNat (";
      printVCExprLean(Expression, OS, LeanTop);
      OS << ").toNat)";
    }
    return;
  }
  LeanEmissionFailed = true;
  printVCExprLean(Expression, OS, LeanArgument);
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
  // Typed: Lean reads a term of numerals alone, such as `2 - 3`, in Nat.
  case VCExpr::IntLit:
    if (E->Sort.Kind == LogicSortKind::BitVector)
      OS << "(BitVec.ofInt " << E->Sort.BitWidth << " (" << E->IntVal << "))";
    else
      OS << "(" << E->IntVal << " : Int)";
    break;
  case VCExpr::Var:
    printLeanName(E->Name, OS);
    break;
  case VCExpr::Not:
    paren(LeanNot, [&] {
      OS << "¬";
      printVCExprLean(E->Children[0].get(), OS, LeanArgument);
    });
    break;
  // Right-associative: only the last operand may be of the same level.
  case VCExpr::And:
    paren(LeanAnd, [&] {
      for (unsigned I = 0; I < E->Children.size(); ++I) {
        if (I)
          OS << " ∧ ";
        printVCExprLean(E->Children[I].get(), OS,
                        I + 1 == E->Children.size() ? LeanAnd : LeanAnd + 1);
      }
    });
    break;
  case VCExpr::Or:
    paren(LeanOr, [&] {
      for (unsigned I = 0; I < E->Children.size(); ++I) {
        if (I)
          OS << " ∨ ";
        printVCExprLean(E->Children[I].get(), OS,
                        I + 1 == E->Children.size() ? LeanOr : LeanOr + 1);
      }
    });
    break;
  case VCExpr::Ite:
    paren(LeanTop, [&] {
      OS << "if ";
      printVCExprLean(E->Children[0].get(), OS, LeanTop);
      OS << " then ";
      printVCExprLean(E->Children[1].get(), OS, LeanTop);
      OS << " else ";
      printVCExprLean(E->Children[2].get(), OS, LeanTop);
    });
    break;
  // Booleans are propositions, equal when equivalent.
  case VCExpr::Eq:
    if (E->Children[0]->Sort.Kind == LogicSortKind::Bool) {
      paren(LeanIff, [&] {
        printVCExprLean(E->Children[0].get(), OS, LeanIff + 1);
        OS << " ↔ ";
        printVCExprLean(E->Children[1].get(), OS, LeanIff + 1);
      });
      break;
    }
    paren(LeanCompare, [&] {
      printVCExprLean(E->Children[0].get(), OS, LeanCompare + 1);
      OS << " = ";
      printVCExprLean(E->Children[1].get(), OS, LeanCompare + 1);
    });
    break;
  case VCExpr::Ne:
    if (E->Children[0]->Sort.Kind == LogicSortKind::Bool) {
      paren(LeanNot, [&] {
        OS << "¬(";
        printVCExprLean(E->Children[0].get(), OS, LeanIff + 1);
        OS << " ↔ ";
        printVCExprLean(E->Children[1].get(), OS, LeanIff + 1);
        OS << ")";
      });
      break;
    }
    paren(LeanCompare, [&] {
      printVCExprLean(E->Children[0].get(), OS, LeanCompare + 1);
      OS << " ≠ ";
      printVCExprLean(E->Children[1].get(), OS, LeanCompare + 1);
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
      printVCExprLean(E->Children[Reverse ? 1 : 0].get(), OS, LeanArgument);
      OS << " ";
      printVCExprLean(E->Children[Reverse ? 0 : 1].get(), OS, LeanArgument);
      OS << ")";
      break;
    }
    paren(LeanCompare, [&] {
      printVCExprLean(E->Children[0].get(), OS, LeanCompare + 1);
      OS << (E->K == VCExpr::Lt   ? " < "
             : E->K == VCExpr::Le ? " ≤ "
             : E->K == VCExpr::Gt ? " > "
                                  : " ≥ ");
      printVCExprLean(E->Children[1].get(), OS, LeanCompare + 1);
    });
    break;
  // Left-associative: a right operand of the same level is parenthesized.
  case VCExpr::Add:
    paren(LeanAdd, [&] {
      printVCExprLean(E->Children[0].get(), OS, LeanAdd);
      OS << " + ";
      printVCExprLean(E->Children[1].get(), OS, LeanAdd + 1);
    });
    break;
  case VCExpr::Sub:
    paren(LeanAdd, [&] {
      printVCExprLean(E->Children[0].get(), OS, LeanAdd);
      OS << " - ";
      printVCExprLean(E->Children[1].get(), OS, LeanAdd + 1);
    });
    break;
  case VCExpr::Mul:
    paren(LeanMul, [&] {
      printVCExprLean(E->Children[0].get(), OS, LeanMul);
      OS << " * ";
      printVCExprLean(E->Children[1].get(), OS, LeanMul + 1);
    });
    break;
  // SMT-LIB's quotient, which the certifier and the solvers use: at a zero
  // divisor all ones unsigned, and -1 or 1 by the dividend's sign signed;
  // Lean's own udiv and sdiv give 0 there.
  case VCExpr::Div:
    OS << "("
       << (E->Sort.Kind == LogicSortKind::BitVector
               ? (E->Sort.Signedness == LogicSignedness::Signed
                      ? "BitVec.smtSDiv "
                      : "BitVec.smtUDiv ")
               : "cppIntDiv ");
    printVCExprLean(E->Children[0].get(), OS, LeanArgument);
    OS << " ";
    printVCExprLean(E->Children[1].get(), OS, LeanArgument);
    OS << ")";
    break;
  case VCExpr::Rem:
    OS << "("
       << (E->Sort.Kind == LogicSortKind::BitVector
               ? (E->Sort.Signedness == LogicSignedness::Signed
                      ? "BitVec.srem "
                      : "BitVec.umod ")
               : "cppIntRem ");
    printVCExprLean(E->Children[0].get(), OS, LeanArgument);
    OS << " ";
    printVCExprLean(E->Children[1].get(), OS, LeanArgument);
    OS << ")";
    break;
  case VCExpr::BitAnd:
  case VCExpr::BitOr:
  case VCExpr::BitXor: {
    const unsigned Level = E->K == VCExpr::BitAnd  ? LeanBitAnd
                           : E->K == VCExpr::BitOr ? LeanBitOr
                                                   : LeanBitXor;
    paren(Level, [&] {
      printVCExprLean(E->Children[0].get(), OS, Level);
      OS << (E->K == VCExpr::BitAnd  ? " &&& "
             : E->K == VCExpr::BitOr ? " ||| "
                                     : " ^^^ ");
      printVCExprLean(E->Children[1].get(), OS, Level + 1);
    });
    break;
  }
  // The amount is capped at the width, which already gives 0: Lean's
  // evaluation computes 2^amount and panics on a 64-bit amount.
  case VCExpr::Shl:
    paren(LeanShift, [&] {
      printVCExprLean(E->Children[0].get(), OS, LeanShift);
      OS << " <<< min (";
      printVCExprLean(E->Children[1].get(), OS, LeanTop);
      OS << ").toNat " << E->Sort.BitWidth;
    });
    break;
  case VCExpr::Shr:
    if (E->Sort.Signedness == LogicSignedness::Signed) {
      OS << "(BitVec.sshiftRight ";
      printVCExprLean(E->Children[0].get(), OS, LeanArgument);
      OS << " (";
      printVCExprLean(E->Children[1].get(), OS, LeanTop);
      OS << ").toNat)";
    } else {
      paren(LeanShift, [&] {
        printVCExprLean(E->Children[0].get(), OS, LeanShift);
        OS << " >>> ";
        printVCExprLean(E->Children[1].get(), OS, LeanShift + 1);
      });
    }
    break;
  // Parenthesized: `f -x y` would parse as a subtraction.
  case VCExpr::Neg:
    OS << "(-";
    printVCExprLean(E->Children[0].get(), OS, LeanArgument);
    OS << ")";
    break;
  case VCExpr::BitNot:
    OS << "(~~~";
    printVCExprLean(E->Children[0].get(), OS, LeanArgument);
    OS << ")";
    break;
  case VCExpr::ValidPtr:
    OS << "(validPtr ";
    printVCExprLean(E->Children[0].get(), OS, LeanArgument);
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
    printVCExprLean(E->Children[0].get(), OS, LeanArgument);
    OS << " ";
    printVCExprLean(E->Children[1].get(), OS, LeanArgument);
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
    printVCExprLean(E->Children[0].get(), OS, LeanArgument);
    OS << " ";
    printVCExprLean(E->Children[1].get(), OS, LeanArgument);
    OS << " ";
    printVCExprLean(E->Children[2].get(), OS, LeanArgument);
    OS << " ";
    printVCExprLean(E->Children[3].get(), OS, LeanArgument);
    OS << ")";
    break;
  case VCExpr::Collection:
    LeanEmissionFailed = true;
    OS << "False";
    break;
  case VCExpr::HeapFrame:
    OS << "(∀ (";
    printLeanName("__frame_address", OS);
    OS << " : Int), ";
    for (unsigned I = 2; I + 1 < E->Children.size(); I += 2) {
      OS << "(";
      printVCExprLean(E->Children[I].get(), OS, LeanCompare + 1);
      OS << " ≤ ";
      printLeanName("__frame_address", OS);
      OS << " ∧ ";
      printLeanName("__frame_address", OS);
      OS << " < ";
      printVCExprLean(E->Children[I + 1].get(), OS, LeanCompare + 1);
      OS << ") ∨ ";
    }
    OS << "heapSelectInt ";
    printVCExprLean(E->Children[1].get(), OS, LeanArgument);
    OS << " ";
    printLeanName("__frame_address", OS);
    OS << " = heapSelectInt ";
    printVCExprLean(E->Children[0].get(), OS, LeanArgument);
    OS << " ";
    printLeanName("__frame_address", OS);
    OS << ")";
    break;
  // A binder extends as far right as it can.
  case VCExpr::Forall:
  case VCExpr::Exists:
    paren(LeanTop, [&] {
      OS << (E->K == VCExpr::Forall ? "∀ (" : "∃ (");
      printLeanName(E->Binder, OS);
      OS << " : Int), ";
      if (E->Children.size() == 1) {
        printVCExprLean(E->Children[0].get(), OS, LeanTop);
        return;
      }
      printVCExprLean(E->Children[0].get(), OS, LeanCompare + 1);
      OS << " ≤ ";
      printLeanName(E->Binder, OS);
      OS << " ∧ ";
      printLeanName(E->Binder, OS);
      OS << " < ";
      printVCExprLean(E->Children[1].get(), OS, LeanCompare + 1);
      OS << (E->K == VCExpr::Forall ? " → " : " ∧ ");
      printVCExprLean(E->Children[2].get(), OS,
                      E->K == VCExpr::Forall ? LeanArrow : LeanAnd);
    });
    break;
  case VCExpr::IntToBv:
    OS << "(BitVec.ofInt " << E->Sort.BitWidth << " (";
    printVCExprLean(E->Children[0].get(), OS, LeanTop);
    OS << "))";
    break;
  case VCExpr::BvToInt:
    if (E->Children[0]->Sort.Signedness == LogicSignedness::Signed) {
      OS << "(";
      printVCExprLean(E->Children[0].get(), OS, LeanTop);
      OS << ").toInt";
    } else {
      OS << "(Int.ofNat (";
      printVCExprLean(E->Children[0].get(), OS, LeanTop);
      OS << ").toNat)";
    }
    break;
  case VCExpr::BvResize:
    OS << "("
       << (E->Children[0]->Sort.Signedness == LogicSignedness::Signed
               ? "BitVec.signExtend "
               : "BitVec.zeroExtend ")
       << E->Sort.BitWidth << " ";
    printVCExprLean(E->Children[0].get(), OS, LeanArgument);
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
         << BitWidth << " (";
      printVCExprLean(E->Children[I].get(), OS, LeanTop);
      OS << "))";
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
    // A subterm shared by several places is named once.
    if (!llvm::is_contained(Nodes, Expression))
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
    printVCExprLean(Expression, OS, LeanTop);
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
    printVCExprLean(Node, OS, LeanTop);
    OS << ";\n  ";
  }
  LeanTemporaryRoot = nullptr;
  printVCExprLean(Expression, OS, LeanTop);
  OS << ")";
  LeanTemporaryNames.clear();
}

static bool mentionsLeanVariable(const LogicExpr *Expression,
                                 llvm::StringRef Name) {
  if (!Expression)
    return false;
  if (Expression->K == LogicExpr::Var && Expression->Name == Name)
    return true;
  return llvm::any_of(Expression->Children, [&](const auto &Child) {
    return mentionsLeanVariable(Child.get(), Name);
  });
}

/// A spec application with the quantifier binders around it that it
/// mentions, outermost first.
struct LeanSpecCall {
  const LogicExpr *Call;
  std::vector<std::string> Binders;
};

static void collectLeanSpecCalls(const LogicExpr *Expression,
                                 std::vector<std::string> &Binders,
                                 std::vector<LeanSpecCall> &Calls) {
  if (!Expression)
    return;
  if (Expression->K == LogicExpr::SpecCall) {
    LeanSpecCall Found{Expression, {}};
    for (const std::string &Binder : Binders)
      if (!llvm::is_contained(Found.Binders, Binder) &&
          mentionsLeanVariable(Expression, Binder))
        Found.Binders.push_back(Binder);
    Calls.push_back(std::move(Found));
  }
  const bool Binds =
      Expression->K == LogicExpr::Forall || Expression->K == LogicExpr::Exists;
  if (Binds)
    Binders.push_back(Expression->Binder);
  for (const auto &Child : Expression->Children)
    collectLeanSpecCalls(Child.get(), Binders, Calls);
  if (Binds)
    Binders.pop_back();
}

// A definition holds at every argument, so the instance at an application
// under quantifiers is stated for every value of their binders.
static unsigned
emitLeanSpecAxiomBinders(const LogicExpr *Goal, llvm::raw_ostream &OS,
                         std::vector<std::string> *Names = nullptr) {
  std::vector<std::string> Binders;
  std::vector<LeanSpecCall> Calls;
  collectLeanSpecCalls(Goal, Binders, Calls);
  unsigned CallIndex = 0;
  unsigned BinderCount = 0;
  for (const auto &[Call, Around] : Calls) {
    const LogicFunctionDecl *Function = findLeanFunction(Call->SpecCallee);
    if (!Function || Call->Children.size() != Function->Parameters.size()) {
      LeanEmissionFailed = true;
      continue;
    }
    ++CallIndex;
    for (unsigned Level = 0; Level < Function->DefinitionFuel; ++Level) {
      ++BinderCount;
      const std::string Axiom = "cppverify_spec_axiom_" +
                                std::to_string(CallIndex) + "_" +
                                std::to_string(Level + 1);
      if (Names)
        Names->push_back(Axiom);
      OS << "\n    (" << Axiom << " : ";
      if (!Around.empty()) {
        OS << "∀";
        for (const std::string &Binder : Around) {
          OS << " (";
          printLeanName(Binder, OS);
          OS << " : Int)";
        }
        OS << ", ";
      }
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

// A hypothesis of a readable goal: an Or that makeGoal joined to the goal,
// whose left operand negates the assumption.
static const LogicExpr *leanHypothesis(const LogicExpr &Premise) {
  const LogicExpr *Left = Premise.Children[0].get();
  return Left->K == LogicExpr::Not && Left->Children.size() == 1
             ? Left->Children[0].get()
             : Left;
}

// Named by where the assumption comes from; a definition by what it defines.
static std::string leanHypothesisName(const LogicExpr &Premise,
                                      std::map<std::string, unsigned> &Counts,
                                      std::set<std::string> &Used) {
  auto [Category, Detail] = llvm::StringRef(Premise.Premise).split(':');
  std::string Base = "h_" + leanIdentifierPart(Category);
  if (!Detail.empty())
    Base += "_" + leanIdentifierPart(Detail);
  bool Numbered = true;
  if (llvm::is_contained({"def", "ret", "branch", "loop", "exit", "fact"},
                         Category)) {
    const LogicExpr *Fact = leanHypothesis(Premise);
    if (Fact != Premise.Children[0].get())
      while (Fact->K == LogicExpr::Or && Fact->Children.size() == 2 &&
             Fact->Children[0]->K == LogicExpr::Not)
        Fact = Fact->Children[1].get();
    if (Fact->K == LogicExpr::Eq && Fact->Children.size() == 2 &&
        Fact->Children[0]->K == LogicExpr::Var) {
      Base = "h_" + llvm::StringRef(leanIdentifierPart(Fact->Children[0]->Name))
                        .ltrim('_')
                        .str();
      Numbered = false;
    }
  }
  std::string Name =
      Numbered ? Base + "_" + std::to_string(++Counts[Base]) : Base;
  while (!Used.insert(Name).second)
    Name = Base + "_" + std::to_string(++Counts[Base]);
  return Name;
}

// The goal as named hypotheses and what remains to be shown, and a proof that
// it implies the goal: the bridge the kernel checks, so a proof of this form
// proves the goal whatever this printer did. Intros receives the names a
// proof of it introduces.
static void emitLeanReadableGoal(llvm::StringRef Name, const LogicExpr *Goal,
                                 const std::map<std::string, LogicSort> &Vars,
                                 bool HasSpecAxioms, std::string &Intros,
                                 llvm::raw_ostream &OS) {
  LeanEmitBudget = 500000;
  std::vector<const LogicExpr *> Premises;
  const LogicExpr *Rest = Goal;
  while (Rest && Rest->K == LogicExpr::Or && !Rest->Premise.empty() &&
         Rest->Children.size() == 2) {
    Premises.push_back(Rest);
    Rest = Rest->Children[1].get();
  }

  std::vector<std::string> Binders;
  for (const auto &[Variable, Sort] : Vars)
    Binders.push_back(encodeLeanName(Variable));
  std::string AxiomText;
  llvm::raw_string_ostream AxiomOS(AxiomText);
  std::vector<std::string> Axioms;
  emitLeanSpecAxiomBinders(Goal, AxiomOS, &Axioms);
  Binders.insert(Binders.end(), Axioms.begin(), Axioms.end());

  LeanTemporaryNames.clear();
  LeanTemporaryRoot = nullptr;
  std::vector<const LogicExpr *> Temporaries;
  for (const LogicExpr *Premise : Premises)
    collectLeanTemporaries(Premise->Children[0].get(), Temporaries, true);
  collectLeanTemporaries(Rest, Temporaries, true);
  std::vector<std::string> Lets;
  for (const LogicExpr *Node : Temporaries) {
    LeanTemporaryNames.emplace(Node, Lets.size() + 1);
    Lets.push_back("__cppverify_term_" + std::to_string(Lets.size() + 1));
  }

  std::set<std::string> Used(Binders.begin(), Binders.end());
  Used.insert(Lets.begin(), Lets.end());
  std::map<std::string, unsigned> Counts;
  std::vector<std::string> Hypotheses;
  for (const LogicExpr *Premise : Premises)
    Hypotheses.push_back(leanHypothesisName(*Premise, Counts, Used));

  OS << "def ";
  printLeanName(Name.str(), OS);
  OS << ".readable";
  OS << " : Prop :=\n  ";
  if (!Vars.empty() || HasSpecAxioms) {
    OS << "∀";
    emitLeanVariableBinders(Vars, OS);
    OS << AxiomText << ",\n    ";
  }
  if (!Lets.empty())
    OS << "(";
  for (const LogicExpr *Node : Temporaries) {
    OS << "let __cppverify_term_" << LeanTemporaryNames.at(Node) << " : ";
    printLeanSort(Node->Sort, OS);
    OS << " := ";
    LeanTemporaryRoot = Node;
    printVCExprLean(Node, OS, LeanTop);
    OS << ";\n    ";
  }
  LeanTemporaryRoot = nullptr;
  for (size_t I = 0; I != Premises.size(); ++I) {
    const LogicExpr *Left = Premises[I]->Children[0].get();
    OS << "(" << Hypotheses[I] << " : ";
    if (leanHypothesis(*Premises[I]) != Left) {
      printVCExprLean(leanHypothesis(*Premises[I]), OS, LeanTop);
    } else {
      OS << "¬";
      printVCExprLean(Left, OS, LeanArgument);
    }
    OS << ") →\n    ";
  }
  printVCExprLean(Rest, OS, Premises.empty() ? LeanTop : LeanArrow);
  if (!Lets.empty())
    OS << ")";
  OS << "\n\n";
  LeanTemporaryNames.clear();

  OS << "theorem ";
  printLeanName(Name.str(), OS);
  OS << ".of_readable (h : ";
  printLeanName(Name.str(), OS);
  OS << ".readable) : ";
  printLeanName(Name.str(), OS);
  OS << " :=\n  ";
  if (!Binders.empty()) {
    OS << "fun";
    for (const std::string &Binder : Binders)
      OS << " " << Binder;
    OS << " =>\n  ";
  }
  for (size_t I = 0; I != Premises.size(); ++I)
    OS << (leanHypothesis(*Premises[I]) != Premises[I]->Children[0].get()
               ? "cppverify_imp_or fun "
               : "cppverify_not_imp_or fun ")
       << Hypotheses[I] << " =>\n  ";
  OS << "h";
  for (const std::string &Binder : Binders)
    OS << " " << Binder;
  for (const std::string &Hypothesis : Hypotheses)
    OS << " " << Hypothesis;
  OS << "\n\n";

  Intros.clear();
  for (const auto *Part : {&Binders, &Lets, &Hypotheses})
    for (const std::string &Introduced : *Part)
      Intros += (Intros.empty() ? "" : " ") + Introduced;
}

static void emitLeanGoalDefinition(llvm::StringRef Name, const LogicExpr *Goal,
                                   llvm::raw_ostream &OS,
                                   std::string *Intros = nullptr) {
  LeanEmitBudget = 500000;
  std::map<std::string, LogicSort> Variables;
  collectLeanVariables(Goal, {}, Variables);
  std::vector<std::string> Binders;
  std::vector<LeanSpecCall> Calls;
  collectLeanSpecCalls(Goal, Binders, Calls);
  bool HasSpecAxioms = false;
  for (const auto &[Call, Around] : Calls)
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
  if (Intros)
    emitLeanReadableGoal(Name, Goal, Variables, HasSpecAxioms, *Intros, OS);
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
    std::vector<LeanProjectGoal> *ProjectGoals,
    const std::set<std::string> *Selection) {
  VerifyResult Result;
  if (!Module.CorrectnessGoal || !Module.CounterexampleQuery) {
    Result.Status = VerifyStatus::Unresolved;
    Result.Reason = VerifyReason::MissingQuery;
    Result.Message = "missing correctness goal for Lean export";
    return Result;
  }

  LeanEmissionFailed = false;
  LeanLogicFunctions = &Module.LogicFunctions;
  // A project names everything by identity, never by position, so that a
  // proof keeps the names it uses when the source around it changes.
  const std::string LegacyBodyPrefix =
      "cppSpecBody_m" + std::to_string(ModuleIndex) + "_";
  LeanBodyPrefix = LegacyBodyPrefix;
  std::string Group;
  if (ProjectGoals) {
    Group = leanProjectGroup(Module);
    LeanBodyPrefix =
        "cppSpecBody_" + leanShortHash(Module.FunctionIdentity, 8) + "_";
    // Modules of one identity (an archive's) are told apart in order.
    for (unsigned Copy = 2; !EmittedTheorems.insert(LeanBodyPrefix).second;
         ++Copy)
      LeanBodyPrefix = "cppSpecBody_" +
                       leanShortHash(Module.FunctionIdentity, 8) + "_" +
                       std::to_string(Copy) + "_";
  }

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
    OS << "abbrev heapSelectBool (h : CppHeap) (p : Int) : Prop := h p ≠ 0\n";
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
    // Reducible, so instance search sees the Bool comparison and decides it.
    OS << "abbrev cppBvUlt {w : Nat} (x y : BitVec w) : Prop := x.ult y = "
          "true\n";
    OS << "abbrev cppBvUle {w : Nat} (x y : BitVec w) : Prop := x.ule y = "
          "true\n";
    OS << "abbrev cppBvSlt {w : Nat} (x y : BitVec w) : Prop := x.slt y = "
          "true\n";
    OS << "abbrev cppBvSle {w : Nat} (x y : BitVec w) : Prop := x.sle y = "
          "true\n\n";
    OS << "def cppIntDiv (x y : Int) : Int :=\n";
    OS << "  if y = 0 then 0 else\n";
    OS << "    let q := (if x < 0 then -x else x) / "
          "(if y < 0 then -y else y)\n";
    OS << "    if (x < 0) ≠ (y < 0) then -q else q\n";
    OS << "def cppIntRem (x y : Int) : Int :=\n";
    OS << "  if y = 0 then x else x - cppIntDiv x y * y\n\n";
    if (ProjectGoals) {
      // What the bridges from readable goals use.
      OS << "theorem cppverify_imp_or {a b : Prop} (h : a → b) : ¬a ∨ b :=\n";
      OS << "  (Classical.em a).elim (fun ha => Or.inr (h ha)) Or.inl\n";
      OS << "theorem cppverify_not_imp_or {a b : Prop} (h : ¬a → b) : a ∨ b "
            ":=\n";
      OS << "  (Classical.em a).elim Or.inl (fun ha => Or.inr (h ha))\n\n";
    }
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
    ++Index;
    const bool Selected = !Selection || Selection->count(Item.Id);
    if (!Selected && !ProjectGoals)
      continue;
    std::string ObligationName =
        TheoremName + "_obligation_" + std::to_string(Index);
    LeanProjectGoal Goal;
    if (ProjectGoals) {
      Goal.Hash = obligationStatementHash(Module, Item);
      Goal.Name = Group + "_" +
                  leanIdentifierPart(obligationKindName(Item.Kind)) + "_" +
                  Goal.Hash.substr(0, 8);
      // Identical obligations of one function, in source order, whichever
      // of them are exported.
      const std::string Base = Goal.Name;
      for (unsigned Copy = 2; !EmittedTheorems.insert(Goal.Name).second; ++Copy)
        Goal.Name = Base + "_" + std::to_string(Copy);
      Goal.Group = Group;
      Goal.StableId = Item.StableId.empty() ? Item.Id : Item.StableId;
      if (Item.Source.isValid()) {
        llvm::raw_string_ostream SourceOS(Goal.Source);
        printLeanCommentText(Item.Source.File, SourceOS);
        SourceOS << ":" << Item.Source.Line << ":" << Item.Source.Column;
      }
      Goal.BodyPrefix = LeanBodyPrefix;
      Goal.LegacyName = encodeLeanName(ObligationName + "_goal");
      Goal.LegacyBodyPrefix = LegacyBodyPrefix;
      Goal.Exported = Selected;
      if (!Selected) {
        ProjectGoals->push_back(std::move(Goal));
        continue;
      }
    }
    OS << "/- obligation: ";
    printLeanCommentText(Item.StableId.empty() ? Item.Id : Item.StableId, OS);
    OS << "\n";
    OS << "   kind: " << obligationKindName(Item.Kind) << "\n";
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
    if (ProjectGoals) {
      emitLeanGoalDefinition(Goal.Name, Item.Goal.get(), OS, &Goal.Intros);
      ProjectGoals->push_back(std::move(Goal));
    } else {
      emitLeanTheorem(ObligationName, Item.Goal.get(), OS);
    }
  }

  if (LeanEmissionFailed) {
    LeanLogicFunctions = nullptr;
    LeanBodyPrefix.clear();
    Result.Status = VerifyStatus::Unresolved;
    Result.Reason = VerifyReason::LeanExportFailure;
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