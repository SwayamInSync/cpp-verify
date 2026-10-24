//===--- LeanBackend.cpp --------------------------------------------------===//
#include "LeanBackend.h"
#include "Certify.h"
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
// Printing a spec's own definition for Lean to accept by well-founded
// recursion: every condition that reaches an application is a hypothesis
// there (`if _h : c`), so that the decrease can be proved from it.
static thread_local bool LeanDefinitionMode = false;

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

// A sequence is a list, a set its membership test, a multiset its counts,
// and a map the value at each key it holds (CppVerify/Prelude.lean).
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
  case LogicSortKind::Seq:
    OS << "List Int";
    return;
  case LogicSortKind::Set:
    OS << "(Int → Bool)";
    return;
  case LogicSortKind::Multiset:
    OS << "(Int → Nat)";
    return;
  case LogicSortKind::Map:
    OS << "(Int → Option Int)";
    return;
  case LogicSortKind::Invalid:
    LeanEmissionFailed = true;
    OS << "False";
    return;
  }
}

// The prelude's function for each collection operation.
static const char *leanCollectionName(LogicCollectionOp Operation) {
  using Op = LogicCollectionOp;
  switch (Operation) {
  case Op::SeqEmpty:
    return "cppSeqEmpty";
  case Op::SeqUnit:
    return "cppSeqUnit";
  case Op::SeqLength:
    return "cppSeqLength";
  case Op::SeqIndex:
    return "cppSeqAt";
  case Op::SeqPush:
    return "cppSeqPush";
  case Op::SeqSubrange:
    return "cppSeqSubrange";
  case Op::SeqConcat:
    return "cppSeqConcat";
  case Op::SeqContains:
    return "cppSeqContains";
  case Op::SetEmpty:
    return "cppSetEmpty";
  case Op::SetInsert:
    return "cppSetInsert";
  case Op::SetRemove:
    return "cppSetRemove";
  case Op::SetContains:
    return "cppSetContains";
  case Op::SetUnion:
    return "cppSetUnion";
  case Op::SetIntersect:
    return "cppSetIntersect";
  case Op::SetDifference:
    return "cppSetDifference";
  case Op::SetSubset:
    return "cppSetSubset";
  case Op::MultisetEmpty:
    return "cppMultisetEmpty";
  case Op::MultisetInsert:
    return "cppMultisetInsert";
  case Op::MultisetRemove:
    return "cppMultisetRemove";
  case Op::MultisetCount:
    return "cppMultisetCount";
  case Op::MapEmpty:
    return "cppMapEmpty";
  case Op::MapInsert:
    return "cppMapInsert";
  case Op::MapRemove:
    return "cppMapRemove";
  case Op::MapContains:
    return "cppMapContains";
  case Op::MapGet:
    return "cppMapGet";
  }
  return nullptr;
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

static bool leanAppliesSpec(const LogicExpr *E) {
  if (!E)
    return false;
  if (E->K == VCExpr::SpecCall)
    return true;
  return llvm::any_of(E->Children, [](const auto &Child) {
    return leanAppliesSpec(Child.get());
  });
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
  // Right-associative: only the last operand may be of the same level. In a
  // definition, the operands before an application are its condition:
  // `a ∧ b` is `if _h : a then b else False`.
  case VCExpr::And:
    if (LeanDefinitionMode)
      for (unsigned I = 1; I < E->Children.size(); ++I)
        if (leanAppliesSpec(E->Children[I].get())) {
          paren(LeanTop, [&] {
            OS << "if _h : ";
            for (unsigned J = 0; J < I; ++J) {
              if (J)
                OS << " ∧ ";
              printVCExprLean(E->Children[J].get(), OS,
                              J + 1 == I ? LeanAnd : LeanAnd + 1);
            }
            OS << " then ";
            for (unsigned J = I; J < E->Children.size(); ++J) {
              if (J != I)
                OS << " ∧ ";
              printVCExprLean(E->Children[J].get(), OS,
                              J + 1 == E->Children.size() ? LeanAnd
                                                          : LeanAnd + 1);
            }
            OS << " else False";
          });
          return;
        }
    paren(LeanAnd, [&] {
      for (unsigned I = 0; I < E->Children.size(); ++I) {
        if (I)
          OS << " ∧ ";
        printVCExprLean(E->Children[I].get(), OS,
                        I + 1 == E->Children.size() ? LeanAnd : LeanAnd + 1);
      }
    });
    break;
  // `a ∨ b` is `if _h : a then True else b`, and `¬a ∨ b` is `if _h : a then b
  // else True`.
  case VCExpr::Or:
    if (LeanDefinitionMode && E->Children.size() > 1 &&
        llvm::any_of(llvm::drop_begin(E->Children), [](const auto &Child) {
          return leanAppliesSpec(Child.get());
        })) {
      paren(LeanTop, [&] {
        const LogicExpr *First = E->Children[0].get();
        const bool Negated = First->K == VCExpr::Not;
        OS << "if _h : ";
        printVCExprLean(Negated ? First->Children[0].get() : First, OS,
                        LeanTop);
        OS << (Negated ? " then " : " then True else ");
        for (unsigned J = 1; J < E->Children.size(); ++J) {
          if (J != 1)
            OS << " ∨ ";
          printVCExprLean(E->Children[J].get(), OS,
                          J + 1 == E->Children.size() ? LeanOr : LeanOr + 1);
        }
        if (Negated)
          OS << " else True";
      });
      break;
    }
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
      OS << (LeanDefinitionMode ? "if _h : " : "if ");
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
  case VCExpr::Collection: {
    const char *Name = leanCollectionName(E->CollectionOp);
    if (!Name) {
      LeanEmissionFailed = true;
      OS << "False";
      break;
    }
    if (E->Children.empty()) {
      OS << Name;
      break;
    }
    OS << "(" << Name;
    for (const auto &Child : E->Children) {
      OS << " ";
      printVCExprLean(Child.get(), OS, LeanArgument);
    }
    OS << ")";
    break;
  }
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
      // In a definition, the range of an existential that applies a spec
      // is its condition, as a universal's is its antecedent.
      const bool Guarded = E->K == VCExpr::Exists && LeanDefinitionMode &&
                           leanAppliesSpec(E->Children[2].get());
      if (Guarded)
        OS << "if _h : ";
      printVCExprLean(E->Children[0].get(), OS, LeanCompare + 1);
      OS << " ≤ ";
      printLeanName(E->Binder, OS);
      OS << " ∧ ";
      printLeanName(E->Binder, OS);
      OS << " < ";
      printVCExprLean(E->Children[1].get(), OS, LeanCompare + 1);
      if (Guarded) {
        OS << " then ";
        printVCExprLean(E->Children[2].get(), OS, LeanTop);
        OS << " else False";
        return;
      }
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

static void collectLeanApplied(const LogicExpr *E,
                               std::set<std::string> &Applied) {
  if (!E)
    return;
  if (E->K == VCExpr::SpecCall)
    Applied.insert(E->SpecCallee);
  for (const auto &Child : E->Children)
    collectLeanApplied(Child.get(), Applied);
}

static std::string leanOpaqueSpec(const LogicFunctionDecl &Function) {
  std::string Text;
  llvm::raw_string_ostream OS(Text);
  OS << "/- spec function: ";
  printLeanCommentText(Function.DisplayName, OS);
  OS << " -/\n";
  OS << "opaque ";
  printLeanSpecName(Function.Identity, OS);
  OS << " : ";
  for (const LogicFunctionParameter &Parameter : Function.Parameters) {
    printLeanSort(Parameter.Sort, OS);
    OS << " -> ";
  }
  printLeanSort(Function.ResultSort, OS);
  OS << "\n\n";
  return Text;
}

// A spec's own definition, for Lean to accept by well-founded recursion: its
// step definition, applying its recursion group by name, every condition
// that reaches an application a hypothesis there, and its termination
// measures, each m as `(m + 1).toNat`: for a caller's m at least 0 and a
// call's below it (it may be -1), the call's is below the caller's, the
// relation the termination check proves, lexicographic over a tuple. None
// for a choice, a function without a definition, or a recursive one without
// measures (an archive's).
static std::string leanSpecDefinition(const ObligationModule &Module,
                                      const LogicFunctionDecl &Function) {
  if (Function.Choice || !Function.StepDefinition)
    return "";
  std::set<std::string> Reached, Pending;
  collectLeanApplied(Function.StepDefinition.get(), Pending);
  while (!Pending.empty()) {
    std::string Next = *Pending.begin();
    Pending.erase(Pending.begin());
    if (!Reached.insert(Next).second)
      continue;
    auto It = Module.LogicFunctions.find(Next);
    if (It != Module.LogicFunctions.end() && It->second.StepDefinition)
      collectLeanApplied(It->second.StepDefinition.get(), Pending);
  }
  const bool Recursive = Reached.count(Function.Identity);
  if (Recursive && Function.Decreases.empty())
    return "";

  const bool FailedBefore = LeanEmissionFailed;
  LeanEmissionFailed = false;
  auto Temporaries = std::move(LeanTemporaryNames);
  LeanTemporaryNames.clear();
  LeanDefinitionMode = true;
  LeanEmitBudget = 1000000;
  std::string Text;
  llvm::raw_string_ostream OS(Text);
  OS << "/- spec function: ";
  printLeanCommentText(Function.DisplayName, OS);
  OS << " -/\n";
  OS << "def ";
  printLeanSpecName(Function.Identity, OS);
  for (const LogicFunctionParameter &Parameter : Function.Parameters) {
    OS << " (";
    printLeanName(Parameter.Name, OS);
    OS << " : ";
    printLeanSort(Parameter.Sort, OS);
    OS << ")";
  }
  OS << " : ";
  printLeanSort(Function.ResultSort, OS);
  OS << " :=\n  ";
  printVCExprLean(Function.StepDefinition.get(), OS, LeanTop);
  if (Recursive) {
    OS << "\ntermination_by ";
    if (Function.Decreases.size() > 1)
      OS << "(";
    for (unsigned I = 0; I < Function.Decreases.size(); ++I) {
      if (I)
        OS << ", ";
      OS << "((";
      printVCExprLean(Function.Decreases[I].get(), OS, LeanTop);
      OS << ") + 1).toNat";
    }
    if (Function.Decreases.size() > 1)
      OS << ")";
    OS << "\ndecreasing_by all_goals cppverify_decreasing";
  }
  OS << "\n\n";
  LeanDefinitionMode = false;
  LeanTemporaryNames = std::move(Temporaries);
  const bool Failed = LeanEmissionFailed;
  LeanEmissionFailed = FailedBefore;
  return Failed ? "" : Text;
}

// A quantifier over a range of integers, as a goal states one, is decided by
// trying each integer of the range, as core Lean decides one over a range of
// naturals, when the range has at most 4096 integers, as many as the
// certifier expands (CertifyLimits::DirectExpansion). Each integer is a level
// of recursion whose memory heartbeats do not count: under the generated
// files' recursion depth a range of 64000 took 58 GB before failing, and one
// of 4000 already spent a step's heartbeats. A larger range has the classical
// instance, which decide cannot evaluate.
static constexpr llvm::StringLiteral LeanBoundedQuantifierPrelude =
    R"lean(instance cppIntBallDecidable (lo hi : Int) (p : Int → Prop) [DecidablePred p] :
    Decidable (∀ x : Int, lo ≤ x ∧ x < hi → p x) :=
  if (hi - lo).toNat ≤ 4096 then
    decidable_of_iff (∀ k : Nat, k < (hi - lo).toNat → p (lo + k)) (by
      constructor
      · intro h x hx
        have := h (x - lo).toNat (by omega)
        rwa [show lo + ((x - lo).toNat : Int) = x by omega] at this
      · intro h k hk
        exact h _ ⟨by omega, by omega⟩)
  else Classical.propDecidable _

instance cppIntBexDecidable (lo hi : Int) (p : Int → Prop) [DecidablePred p] :
    Decidable (∃ x : Int, lo ≤ x ∧ x < hi ∧ p x) :=
  if (hi - lo).toNat ≤ 4096 then
    decidable_of_iff (∃ k : Nat, k < (hi - lo).toNat ∧ p (lo + k)) (by
      constructor
      · rintro ⟨k, hk, hp⟩
        exact ⟨lo + k, by omega, by omega, hp⟩
      · rintro ⟨x, h1, h2, hp⟩
        refine ⟨(x - lo).toNat, by omega, ?_⟩
        rwa [show lo + ((x - lo).toNat : Int) = x by omega])
  else Classical.propDecidable _

)lean";

static void emitLeanFunctionDeclarations(
    const ObligationModule &Module, llvm::raw_ostream &OS,
    std::set<std::string> &EmittedFunctions,
    std::map<std::string, LeanSpecDeclaration> *Specs) {
  for (const auto &[Identity, Function] : Module.LogicFunctions) {
    if (Specs) {
      auto [It, Inserted] = Specs->try_emplace(Identity);
      LeanSpecDeclaration &Declaration = It->second;
      if (Inserted) {
        llvm::raw_string_ostream Name(Declaration.Name);
        printLeanSpecName(Identity, Name);
        Declaration.Opaque = leanOpaqueSpec(Function);
      }
      if (Declaration.Definition.empty()) {
        Declaration.Definition = leanSpecDefinition(Module, Function);
        Declaration.Applies.clear();
        collectLeanApplied(Function.StepDefinition.get(), Declaration.Applies);
      }
      continue;
    }
    if (EmittedFunctions.insert(Identity).second)
      OS << leanOpaqueSpec(Function);
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

// Collections of mathematical integers, with the total meaning <cppverify.h>
// gives each operation, and lemmas that state it for simp, grind, and proofs
// by hand. Checking a goal never needs them: they are theorems of the
// definitions.
static constexpr llvm::StringLiteral LeanCollectionPrelude =
    R"lean(/- Collections of mathematical integers, total as <cppverify.h> defines
   them: a sequence is a list, a set its membership test, a multiset its
   counts, and a map the value at each key it holds. -/

def cppSeqEmpty : List Int := []
def cppSeqUnit (x : Int) : List Int := [x]
def cppSeqLength (s : List Int) : Int := s.length
def cppSeqAt (s : List Int) (i : Int) : Int :=
  if i < 0 then 0 else s[i.toNat]?.getD 0
def cppSeqPush (s : List Int) (x : Int) : List Int := s ++ [x]
def cppSeqConcat (s t : List Int) : List Int := s ++ t
def cppSeqSubrange (s : List Int) (lo hi : Int) : List Int :=
  (s.drop (max 0 (min lo s.length)).toNat).take
    (max (max 0 (min lo s.length)) (min hi s.length) -
      max 0 (min lo s.length)).toNat
def cppSeqContains (s : List Int) (x : Int) : Prop := x ∈ s
instance (s : List Int) (x : Int) : Decidable (cppSeqContains s x) :=
  inferInstanceAs (Decidable (x ∈ s))

def cppSetEmpty : Int → Bool := fun _ => false
def cppSetInsert (s : Int → Bool) (x : Int) : Int → Bool :=
  fun y => y == x || s y
def cppSetRemove (s : Int → Bool) (x : Int) : Int → Bool :=
  fun y => y != x && s y
def cppSetContains (s : Int → Bool) (x : Int) : Prop := s x = true
instance (s : Int → Bool) (x : Int) : Decidable (cppSetContains s x) :=
  inferInstanceAs (Decidable (s x = true))
def cppSetUnion (s t : Int → Bool) : Int → Bool := fun y => s y || t y
def cppSetIntersect (s t : Int → Bool) : Int → Bool := fun y => s y && t y
def cppSetDifference (s t : Int → Bool) : Int → Bool :=
  fun y => s y && !t y
def cppSetSubset (s t : Int → Bool) : Prop := ∀ y, s y = true → t y = true

def cppMultisetEmpty : Int → Nat := fun _ => 0
def cppMultisetInsert (m : Int → Nat) (x : Int) : Int → Nat :=
  fun y => if y = x then m y + 1 else m y
def cppMultisetRemove (m : Int → Nat) (x : Int) : Int → Nat :=
  fun y => if y = x then m y - 1 else m y
def cppMultisetCount (m : Int → Nat) (x : Int) : Int := m x

def cppMapEmpty : Int → Option Int := fun _ => none
def cppMapInsert (m : Int → Option Int) (k v : Int) : Int → Option Int :=
  fun y => if y = k then some v else m y
def cppMapRemove (m : Int → Option Int) (k : Int) : Int → Option Int :=
  fun y => if y = k then none else m y
def cppMapContains (m : Int → Option Int) (k : Int) : Prop :=
  (m k).isSome = true
instance (m : Int → Option Int) (k : Int) : Decidable (cppMapContains m k) :=
  inferInstanceAs (Decidable ((m k).isSome = true))
def cppMapGet (m : Int → Option Int) (k : Int) : Int := (m k).getD 0

/- What each operation means, for simp, grind, and proofs by hand. -/

private theorem cppverify_ite_pos {c : Prop} [Decidable c] {α : Sort _}
    {a b : α} (h : c) : (if c then a else b) = a := by simp [h]
private theorem cppverify_ite_neg {c : Prop} [Decidable c] {α : Sort _}
    {a b : α} (h : ¬c) : (if c then a else b) = b := by simp [h]

@[simp, grind =] theorem cppSeqLength_empty : cppSeqLength cppSeqEmpty = 0 := rfl
@[simp, grind =] theorem cppSeqLength_unit (x : Int) :
    cppSeqLength (cppSeqUnit x) = 1 := rfl
@[simp, grind =] theorem cppSeqLength_push (s : List Int) (x : Int) :
    cppSeqLength (cppSeqPush s x) = cppSeqLength s + 1 := by
  simp [cppSeqLength, cppSeqPush]
@[simp, grind =] theorem cppSeqLength_concat (s t : List Int) :
    cppSeqLength (cppSeqConcat s t) = cppSeqLength s + cppSeqLength t := by
  simp [cppSeqLength, cppSeqConcat]
theorem cppSeqLength_nonneg (s : List Int) : 0 ≤ cppSeqLength s := by
  simp [cppSeqLength]
grind_pattern cppSeqLength_nonneg => cppSeqLength s
@[simp, grind =] theorem cppSeqLength_subrange (s : List Int) (lo hi : Int) :
    cppSeqLength (cppSeqSubrange s lo hi) =
      max (max 0 (min lo (cppSeqLength s))) (min hi (cppSeqLength s)) -
        max 0 (min lo (cppSeqLength s)) := by
  simp only [cppSeqLength, cppSeqSubrange, List.length_take, List.length_drop]
  omega

theorem cppSeqAt_out (s : List Int) (i : Int)
    (h : i < 0 ∨ cppSeqLength s ≤ i) : cppSeqAt s i = 0 := by
  unfold cppSeqAt cppSeqLength at *
  split
  · rfl
  · rw [List.getElem?_eq_none (by omega)]; rfl
@[simp, grind =] theorem cppSeqAt_empty (i : Int) : cppSeqAt cppSeqEmpty i = 0 :=
  cppSeqAt_out [] i (by simp [cppSeqLength]; omega)
@[simp, grind =] theorem cppSeqAt_push (s : List Int) (x i : Int) :
    cppSeqAt (cppSeqPush s x) i =
      if i = cppSeqLength s then x else cppSeqAt s i := by
  unfold cppSeqAt cppSeqPush cppSeqLength
  by_cases h0 : i < 0
  · simp only [h0, ↓reduceIte, show ¬ i = (s.length : Int) by omega]
  · by_cases he : i = s.length
    · subst he; simp only [h0, ↓reduceIte]; simp
    · simp only [h0, he, ↓reduceIte]
      by_cases hl : i.toNat < s.length
      · rw [List.getElem?_append_left hl]
      · rw [List.getElem?_append_right (by omega),
          List.getElem?_eq_none (show s.length ≤ i.toNat by omega),
          List.getElem?_eq_none (by simp; omega)]
@[simp, grind =] theorem cppSeqAt_concat (s t : List Int) (i : Int) :
    cppSeqAt (cppSeqConcat s t) i =
      if i < cppSeqLength s then cppSeqAt s i
      else cppSeqAt t (i - cppSeqLength s) := by
  unfold cppSeqAt cppSeqLength cppSeqConcat
  by_cases h0 : i < 0
  · simp only [h0, ↓reduceIte, show i < (s.length : Int) by omega]
  · by_cases hl : i < s.length
    · simp only [h0, hl, ↓reduceIte]
      rw [List.getElem?_append_left (by omega)]
    · simp only [h0, hl, ↓reduceIte, show ¬ (i - s.length < 0) by omega]
      rw [List.getElem?_append_right (by omega)]
      congr 3; omega
@[simp, grind =] theorem cppSeqAt_unit (x i : Int) :
    cppSeqAt (cppSeqUnit x) i = if i = 0 then x else 0 := by
  unfold cppSeqAt cppSeqUnit
  by_cases h0 : i < 0
  · simp only [h0, ↓reduceIte, show ¬ i = 0 by omega]
  · by_cases h : i = 0
    · subst h; simp
    · simp only [h0, h, ↓reduceIte]
      rw [List.getElem?_eq_none (by simp; omega)]; rfl
@[simp, grind =] theorem cppSeqAt_subrange (s : List Int) (lo hi i : Int) :
    cppSeqAt (cppSeqSubrange s lo hi) i =
      if 0 ≤ i ∧ i < cppSeqLength (cppSeqSubrange s lo hi)
      then cppSeqAt s (max 0 (min lo (cppSeqLength s)) + i) else 0 := by
  rw [cppSeqLength_subrange]
  unfold cppSeqAt cppSeqSubrange cppSeqLength
  by_cases h0 : i < 0
  · simp only [h0, ↓reduceIte, show ¬ (0 ≤ i) by omega, false_and]
  · simp only [h0, ↓reduceIte]
    split
    · rw [List.getElem?_take, cppverify_ite_pos (by omega), List.getElem?_drop,
        cppverify_ite_neg (show ¬ (max 0 (min lo (s.length : Int)) + i < 0) by omega)]
      congr 3; omega
    · rw [List.getElem?_take, cppverify_ite_neg (by omega)]; rfl
@[simp, grind =] theorem cppSeqContains_empty (x : Int) :
    cppSeqContains cppSeqEmpty x ↔ False := by
  simp [cppSeqContains, cppSeqEmpty]
@[simp, grind =] theorem cppSeqContains_unit (y x : Int) :
    cppSeqContains (cppSeqUnit y) x ↔ x = y := by
  simp [cppSeqContains, cppSeqUnit]
@[simp, grind =] theorem cppSeqContains_push (s : List Int) (y x : Int) :
    cppSeqContains (cppSeqPush s y) x ↔ cppSeqContains s x ∨ x = y := by
  simp [cppSeqContains, cppSeqPush]
@[simp, grind =] theorem cppSeqContains_concat (s t : List Int) (x : Int) :
    cppSeqContains (cppSeqConcat s t) x ↔
      cppSeqContains s x ∨ cppSeqContains t x := by
  simp [cppSeqContains, cppSeqConcat]
@[simp, grind =] theorem cppSeqSubrange_all (s : List Int) :
    cppSeqSubrange s 0 (cppSeqLength s) = s := by
  unfold cppSeqSubrange cppSeqLength
  rw [show (max 0 (min (0 : Int) (s.length : Int))).toNat = 0 by omega,
    show (max (max 0 (min (0 : Int) (s.length : Int)))
        (min (s.length : Int) (s.length : Int)) -
        max 0 (min (0 : Int) (s.length : Int))).toNat = s.length by omega]
  simp
@[simp, grind =] theorem cppSeqSubrange_concat_left (s t : List Int) :
    cppSeqSubrange (cppSeqConcat s t) 0 (cppSeqLength s) = s := by
  unfold cppSeqSubrange cppSeqConcat cppSeqLength
  have hl : (s ++ t).length = s.length + t.length := List.length_append
  rw [show (max 0 (min (0 : Int) ((s ++ t).length : Int))).toNat = 0 by omega,
    show (max (max 0 (min (0 : Int) ((s ++ t).length : Int)))
        (min (s.length : Int) ((s ++ t).length : Int)) -
        max 0 (min (0 : Int) ((s ++ t).length : Int))).toNat = s.length by
      omega]
  simp
@[simp, grind =] theorem cppSeqSubrange_concat_right (s t : List Int) :
    cppSeqSubrange (cppSeqConcat s t) (cppSeqLength s)
      (cppSeqLength s + cppSeqLength t) = t := by
  unfold cppSeqSubrange cppSeqConcat cppSeqLength
  have hl : (s ++ t).length = s.length + t.length := List.length_append
  rw [show (max 0 (min (s.length : Int) ((s ++ t).length : Int))).toNat =
      s.length by omega,
    show (max (max 0 (min (s.length : Int) ((s ++ t).length : Int)))
        (min ((s.length : Int) + (t.length : Int)) ((s ++ t).length : Int)) -
        max 0 (min (s.length : Int) ((s ++ t).length : Int))).toNat =
      t.length by omega]
  simp
@[simp, grind =] theorem cppSeqSubrange_push (s : List Int) (x : Int) :
    cppSeqSubrange (cppSeqPush s x) 0 (cppSeqLength s) = s :=
  cppSeqSubrange_concat_left s [x]
theorem cppSeqContains_iff (s : List Int) (x : Int) :
    cppSeqContains s x ↔
      ∃ i, 0 ≤ i ∧ i < cppSeqLength s ∧ cppSeqAt s i = x := by
  unfold cppSeqContains cppSeqLength cppSeqAt
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, he⟩
    refine ⟨i, by omega, by omega, ?_⟩
    rw [cppverify_ite_neg (by omega), Int.toNat_natCast, List.getElem?_eq_getElem hi]
    simpa using he
  · rintro ⟨i, h0, hl, he⟩
    refine ⟨i.toNat, by omega, ?_⟩
    rw [cppverify_ite_neg (by omega), List.getElem?_eq_getElem (by omega)] at he
    simpa using he
theorem cppSeq_ext (s t : List Int) (hl : cppSeqLength s = cppSeqLength t)
    (h : ∀ i, 0 ≤ i → i < cppSeqLength s → cppSeqAt s i = cppSeqAt t i) :
    s = t := by
  unfold cppSeqLength at hl
  apply List.ext_getElem (by omega)
  intro i h1 h2
  have := h i (by omega) (by unfold cppSeqLength; omega)
  unfold cppSeqAt at this
  simp only [show ¬ ((i : Int) < 0) by omega, ↓reduceIte, Int.toNat_natCast,
    List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2,
    Option.getD_some] at this
  exact this

@[simp, grind =] theorem cppSetContains_empty (x : Int) :
    cppSetContains cppSetEmpty x ↔ False := by simp [cppSetContains, cppSetEmpty]
@[simp, grind =] theorem cppSetContains_insert (s : Int → Bool) (x y : Int) :
    cppSetContains (cppSetInsert s x) y ↔ y = x ∨ cppSetContains s y := by
  simp [cppSetContains, cppSetInsert]
@[simp, grind =] theorem cppSetContains_remove (s : Int → Bool) (x y : Int) :
    cppSetContains (cppSetRemove s x) y ↔ y ≠ x ∧ cppSetContains s y := by
  simp [cppSetContains, cppSetRemove]
@[simp, grind =] theorem cppSetContains_union (s t : Int → Bool) (y : Int) :
    cppSetContains (cppSetUnion s t) y ↔
      cppSetContains s y ∨ cppSetContains t y := by
  simp [cppSetContains, cppSetUnion]
@[simp, grind =] theorem cppSetContains_intersect (s t : Int → Bool) (y : Int) :
    cppSetContains (cppSetIntersect s t) y ↔
      cppSetContains s y ∧ cppSetContains t y := by
  simp [cppSetContains, cppSetIntersect]
@[simp, grind =] theorem cppSetContains_difference (s t : Int → Bool) (y : Int) :
    cppSetContains (cppSetDifference s t) y ↔
      cppSetContains s y ∧ ¬ cppSetContains t y := by
  simp [cppSetContains, cppSetDifference]
@[simp, grind =] theorem cppSetSubset_iff (s t : Int → Bool) :
    cppSetSubset s t ↔ ∀ y, cppSetContains s y → cppSetContains t y := Iff.rfl
theorem cppSet_ext (s t : Int → Bool)
    (h : ∀ y, cppSetContains s y ↔ cppSetContains t y) : s = t := by
  funext y
  have := h y
  unfold cppSetContains at this
  cases hs : s y <;> cases ht : t y <;> simp_all

@[simp, grind =] theorem cppMultisetCount_empty (x : Int) :
    cppMultisetCount cppMultisetEmpty x = 0 := rfl
@[simp, grind =] theorem cppMultisetCount_insert (m : Int → Nat) (x y : Int) :
    cppMultisetCount (cppMultisetInsert m x) y =
      if y = x then cppMultisetCount m y + 1 else cppMultisetCount m y := by
  unfold cppMultisetCount cppMultisetInsert; split <;> simp
@[simp, grind =] theorem cppMultisetCount_remove (m : Int → Nat) (x y : Int) :
    cppMultisetCount (cppMultisetRemove m x) y =
      if y = x then max 0 (cppMultisetCount m y - 1)
      else cppMultisetCount m y := by
  unfold cppMultisetCount cppMultisetRemove; split <;> omega
theorem cppMultisetCount_nonneg (m : Int → Nat) (x : Int) :
    0 ≤ cppMultisetCount m x := by simp [cppMultisetCount]
grind_pattern cppMultisetCount_nonneg => cppMultisetCount m x
theorem cppMultiset_ext (m n : Int → Nat)
    (h : ∀ y, cppMultisetCount m y = cppMultisetCount n y) : m = n := by
  funext y; have := h y; unfold cppMultisetCount at this; omega

@[simp, grind =] theorem cppMapContains_empty (k : Int) :
    cppMapContains cppMapEmpty k ↔ False := by simp [cppMapContains, cppMapEmpty]
@[simp, grind =] theorem cppMapContains_insert (m : Int → Option Int) (k v y : Int) :
    cppMapContains (cppMapInsert m k v) y ↔ y = k ∨ cppMapContains m y := by
  unfold cppMapContains cppMapInsert; by_cases h : y = k <;> simp [h]
@[simp, grind =] theorem cppMapContains_remove (m : Int → Option Int) (k y : Int) :
    cppMapContains (cppMapRemove m k) y ↔ y ≠ k ∧ cppMapContains m y := by
  unfold cppMapContains cppMapRemove; by_cases h : y = k <;> simp [h]
@[simp, grind =] theorem cppMapGet_empty (k : Int) : cppMapGet cppMapEmpty k = 0 := rfl
@[simp, grind =] theorem cppMapGet_insert (m : Int → Option Int) (k v y : Int) :
    cppMapGet (cppMapInsert m k v) y = if y = k then v else cppMapGet m y := by
  unfold cppMapGet cppMapInsert; split <;> simp
@[simp, grind =] theorem cppMapGet_remove (m : Int → Option Int) (k y : Int) :
    cppMapGet (cppMapRemove m k) y = if y = k then 0 else cppMapGet m y := by
  unfold cppMapGet cppMapRemove; split <;> simp
theorem cppMapGet_out (m : Int → Option Int) (k : Int)
    (h : ¬ cppMapContains m k) : cppMapGet m k = 0 := by
  unfold cppMapGet; unfold cppMapContains at h; cases hm : m k <;> simp_all
theorem cppMap_ext (m n : Int → Option Int)
    (hc : ∀ y, cppMapContains m y ↔ cppMapContains n y)
    (hg : ∀ y, cppMapGet m y = cppMapGet n y) : m = n := by
  funext y
  have c := hc y; have g := hg y
  unfold cppMapGet at g
  unfold cppMapContains at c
  cases hm : m y <;> cases hn : n y <;> simp_all

)lean";

// The definitions every exported goal is stated with: the heap model, the
// machine comparisons, C++ division, and the collections; a project's goals
// also have the lemmas their readable forms' bridges use.
void verify::emitLeanPrelude(llvm::raw_ostream &OS, bool Project) {
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
  OS << LeanBoundedQuantifierPrelude;
  OS << LeanCollectionPrelude;
  OS << "/- Proves that an application in a spec's definition lowers its "
        "measure. -/\n";
  OS << "macro \"cppverify_decreasing\" : tactic => `(tactic| first\n";
  OS << "  | (simp_wf; omega)\n";
  OS << "  | (simp_wf; simp only [cppSeqLength, cppMultisetCount, cppBvSlt, "
        "cppBvSle,\n";
  OS << "      cppBvUlt, cppBvUle] at *; omega)\n";
  // C++ division and remainder by a constant, which omega reads once the
  // signs are split.
  OS << "  | (simp_wf; simp only [cppIntDiv, cppIntRem] at *;\n";
  OS << "      (repeat' split) <;> simp_all <;> omega)\n";
  OS << "  | (simp_wf; simp_all; omega)\n";
  OS << "  | decreasing_tactic)\n\n";
  if (Project) {
    // What the bridges from readable goals use.
    OS << "theorem cppverify_imp_or {a b : Prop} (h : a → b) : ¬a ∨ b :=\n";
    OS << "  (Classical.em a).elim (fun ha => Or.inr (h ha)) Or.inl\n";
    OS << "theorem cppverify_not_imp_or {a b : Prop} (h : ¬a → b) : a ∨ b "
          ":=\n";
    OS << "  (Classical.em a).elim Or.inl (fun ha => Or.inr (h ha))\n\n";
  }
}

// A piecewise-constant function of the integers as a Lean term: the cell
// of each address, from the run it lies in.
static void printLeanRuns(const HeapValue &Runs, llvm::StringRef Before,
                          llvm::StringRef After, llvm::raw_ostream &OS) {
  OS << "(fun (a : Int) => ";
  for (auto It = Runs.Breaks.rbegin(); It != Runs.Breaks.rend(); ++It)
    OS << "if a ≥ (" << It->first.toDecimal() << " : Int) then " << Before
       << It->second.toDecimal() << After << " else ";
  OS << Before << Runs.Default.toDecimal() << After << ")";
}

// A model's value as a Lean term of its sort; false when it has none.
static bool printLeanValue(const LogicValue &Value, const LogicSort &Sort,
                           llvm::raw_ostream &OS) {
  switch (Sort.Kind) {
  case LogicSortKind::Bool:
    if (Value.K != LogicValue::Kind::Bool)
      return false;
    OS << (Value.Truth ? "True" : "False");
    return true;
  case LogicSortKind::MathematicalInteger:
  case LogicSortKind::Pointer:
    if (Value.K != LogicValue::Kind::Integer)
      return false;
    OS << "(" << Value.Integer.toDecimal() << " : Int)";
    return true;
  case LogicSortKind::BitVector:
    if (Value.K != LogicValue::Kind::Integer)
      return false;
    OS << "(BitVec.ofInt " << Sort.BitWidth << " (" << Value.Integer.toDecimal()
       << "))";
    return true;
  case LogicSortKind::Heap:
    if (Value.K != LogicValue::Kind::Heap || !Value.Heap)
      return false;
    printLeanRuns(*Value.Heap, "(", " : Int)", OS);
    return true;
  case LogicSortKind::Seq:
    if (Value.K != LogicValue::Kind::Seq || !Value.Elements)
      return false;
    OS << "([";
    for (size_t I = 0; I != Value.Elements->size(); ++I)
      OS << (I ? ", " : "") << "(" << (*Value.Elements)[I].toDecimal()
         << " : Int)";
    OS << "] : List Int)";
    return true;
  case LogicSortKind::Set:
    if (Value.K != LogicValue::Kind::Set || !Value.Heap)
      return false;
    printLeanRuns(*Value.Heap, "decide ((", " : Int) ≠ 0)", OS);
    return true;
  case LogicSortKind::Multiset:
    if (Value.K != LogicValue::Kind::Multiset || !Value.Heap)
      return false;
    printLeanRuns(*Value.Heap, "((", " : Int).toNat)", OS);
    return true;
  case LogicSortKind::Map:
    if (Value.K != LogicValue::Kind::Map || !Value.Heap || !Value.Values)
      return false;
    OS << "(fun (k : Int) => if ";
    printLeanRuns(*Value.Heap, "(", " : Int)", OS);
    OS << " k ≠ 0 then some (";
    printLeanRuns(*Value.Values, "(", " : Int)", OS);
    OS << " k) else none)";
    return true;
  case LogicSortKind::Invalid:
    return false;
  }
  return false;
}

VerifyResult verify::exportLeanScratchPad(
    const ObligationModule &Module, llvm::raw_ostream &OS, bool EmitPreamble,
    std::set<std::string> &EmittedFunctions,
    std::set<std::string> &EmittedTheorems, unsigned ModuleIndex,
    std::vector<LeanProjectGoal> *ProjectGoals,
    const std::set<std::string> *Selection,
    std::map<std::string, LeanSpecDeclaration> *Specs) {
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
    emitLeanPrelude(OS, ProjectGoals != nullptr);
  }

  emitLeanFunctionDeclarations(Module, OS, EmittedFunctions, Specs);
  emitLeanFunctionBodies(Module, OS);
  OS << "/- function: ";
  printLeanCommentText(Module.FunctionName, OS);
  OS << " -/\n";
  OS << "/- required logic: " << formatLogicFeatures(Module.RequiredFeatures)
     << " -/\n";
  if (Module.BMCTransform)
    OS << "/- bound: " << Module.BMCTransform->UnrollBound
       << " loop iterations, by unrolling: these goals speak only of the\n"
          "   executions within them, and an unwinding goal says that every "
          "loop\n   ends within them -/\n";
  OS << "\n";

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
      Goal.Unwinding = Item.Kind == ObligationKind::Unwinding;
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

std::optional<LeanRefutation> verify::exportLeanRefutation(
    const ObligationModule &Module, const Obligation &Item,
    const CounterexampleAssignment &Assignment,
    std::map<std::string, LeanSpecDeclaration> &Specs, std::string &Why) {
  // The goal, its bodies, and its specs as its project states them.
  std::string Goals;
  llvm::raw_string_ostream GoalsOS(Goals);
  std::set<std::string> Functions, Theorems;
  std::vector<LeanProjectGoal> Stated;
  const std::set<std::string> Selection = {Item.Id};
  VerifyResult Exported = exportLeanScratchPad(
      Module, GoalsOS, /*EmitPreamble=*/false, Functions, Theorems,
      /*ModuleIndex=*/1, &Stated, &Selection, &Specs);
  auto Goal = llvm::find_if(
      Stated, [](const LeanProjectGoal &Goal) { return Goal.Exported; });
  if (Exported.Status != VerifyStatus::Exported || Goal == Stated.end()) {
    Why = Exported.Message.empty() ? "the goal has no Lean statement"
                                   : Exported.Message;
    return std::nullopt;
  }

  // The goal applied to the values of its variables, in the order it binds
  // them; the definition instances it states then hold by evaluation.
  std::string Application;
  llvm::raw_string_ostream ApplicationOS(Application);
  std::map<std::string, LogicSort> Variables;
  collectLeanVariables(Item.Goal.get(), {}, Variables);
  for (const auto &[Name, Sort] : Variables) {
    auto Value = Assignment.Values.find(Name);
    ApplicationOS << "\n    ";
    if (Value == Assignment.Values.end() ||
        !printLeanValue(Value->second, Sort, ApplicationOS)) {
      Why = "the counterexample gives " + Name + " no value Lean can state";
      return std::nullopt;
    }
  }

  LeanRefutation Refutation;
  Refutation.Group = Goal->Group;
  Refutation.Goal = Goal->Name;
  Refutation.StableId = Goal->StableId;
  llvm::raw_string_ostream OS(Refutation.Text);
  OS << "import CppVerify.Specs\nimport CppVerify.Auto\n\n"
     << "noncomputable section\n\nset_option maxRecDepth 100000\n"
     << "set_option linter.unusedVariables false\n\n"
     << "section Goal\n\nset_option maxHeartbeats 0\n\n"
     << "attribute [local instance] cppVerifyPropDecidable\n\n"
     << Goals << "end Goal\n\n"
     << "/- The goal is false at the counterexample of "
     << (Item.StableId.empty() ? Item.Id : Item.StableId) << ". -/\n"
     << "theorem " << Goal->Name << "_refuted : ¬ " << Goal->Name
     << " := by\n  intro h\n  have h₁ := h" << Application
     << "\n  cppverify_refute h₁\n";
  return Refutation;
}