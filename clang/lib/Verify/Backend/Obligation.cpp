//===--- Obligation.cpp ---------------------------------------------------===//
#include "ObligationLowering.h"
#include "SpecAxioms.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include <algorithm>

using namespace clang;
using namespace verify;

LogicSort LogicSort::boolSort() {
  return {LogicSortKind::Bool, 0, LogicSignedness::None};
}

LogicSort LogicSort::mathematicalInteger(unsigned BitWidth, bool IsSigned) {
  return {LogicSortKind::MathematicalInteger, BitWidth,
          IsSigned ? LogicSignedness::Signed : LogicSignedness::Unsigned};
}

LogicSort LogicSort::bitVector(unsigned BitWidth, bool IsSigned) {
  return {LogicSortKind::BitVector, BitWidth,
          IsSigned ? LogicSignedness::Signed : LogicSignedness::Unsigned};
}

LogicSort LogicSort::pointer() {
  return {LogicSortKind::Pointer, 0, LogicSignedness::Unsigned};
}

LogicSort LogicSort::heap() {
  return {LogicSortKind::Heap, 0, LogicSignedness::None};
}

const char *verify::logicSortName(LogicSortKind Kind) {
  switch (Kind) {
  case LogicSortKind::Invalid:
    return "invalid";
  case LogicSortKind::Bool:
    return "bool";
  case LogicSortKind::MathematicalInteger:
    return "int";
  case LogicSortKind::BitVector:
    return "bitvector";
  case LogicSortKind::Pointer:
    return "pointer";
  case LogicSortKind::Heap:
    return "heap";
  }
  return "invalid";
}

std::string verify::formatLogicSort(const LogicSort &Sort) {
  switch (Sort.Kind) {
  case LogicSortKind::Invalid:
    return "invalid";
  case LogicSortKind::Bool:
    return "bool";
  case LogicSortKind::MathematicalInteger:
    return std::string(Sort.Signedness == LogicSignedness::Signed ? "math-i"
                                                                  : "math-u") +
           std::to_string(Sort.BitWidth);
  case LogicSortKind::BitVector:
    return std::string(Sort.Signedness == LogicSignedness::Signed ? "i" : "u") +
           std::to_string(Sort.BitWidth);
  case LogicSortKind::Pointer:
    return "pointer";
  case LogicSortKind::Heap:
    return "heap";
  }
  return "invalid";
}

std::string verify::formatLogicFeatures(LogicFeatureSet Features) {
  struct NamedFeature {
    LogicFeature Feature;
    const char *Name;
  };
  static constexpr NamedFeature Names[] = {
      {LogicFeature::MathematicalIntegers, "mathematical-integers"},
      {LogicFeature::BitVectors, "bit-vectors"},
      {LogicFeature::Pointers, "pointers"},
      {LogicFeature::HeapArrays, "heap-arrays"},
      {LogicFeature::Quantifiers, "quantifiers"},
      {LogicFeature::SpecFunctions, "spec-functions"},
  };
  std::string Result;
  for (const NamedFeature &Named : Names) {
    if (!(Features & logicFeature(Named.Feature)))
      continue;
    if (!Result.empty())
      Result += ", ";
    Result += Named.Name;
  }
  return Result.empty() ? "none" : Result;
}

static LogicSort logicSortFor(VTypeKind Kind, VIntMode Mode, unsigned BitWidth,
                              bool IsSigned) {
  if (Kind == VTypeKind::Bool)
    return LogicSort::boolSort();
  if (Kind == VTypeKind::Ptr)
    return LogicSort::pointer();
  if (Kind != VTypeKind::Int32 && Kind != VTypeKind::Int64)
    return {};
  if (Mode == VIntMode::Math)
    return LogicSort::mathematicalInteger(BitWidth, IsSigned);
  return LogicSort::bitVector(BitWidth, IsSigned);
}

static LogicOverflowOp logicOverflowOp(VOverflowOp Op) {
  switch (Op) {
  case VOverflowOp::Add:
    return LogicOverflowOp::Add;
  case VOverflowOp::Sub:
    return LogicOverflowOp::Sub;
  case VOverflowOp::Mul:
    return LogicOverflowOp::Mul;
  case VOverflowOp::Neg:
    return LogicOverflowOp::Neg;
  case VOverflowOp::SDiv:
    return LogicOverflowOp::SignedDiv;
  }
  llvm_unreachable("unknown VCR overflow operation");
}

static ObligationKind obligationKind(ProofObligationKind Kind) {
  switch (Kind) {
  case ProofObligationKind::Assertion:
    return ObligationKind::Assertion;
  case ProofObligationKind::Postcondition:
    return ObligationKind::Postcondition;
  case ProofObligationKind::Unwinding:
    return ObligationKind::Unwinding;
  }
  llvm_unreachable("unknown VCR proof-obligation kind");
}

static void setBoolSort(VCExpr &Expr) { Expr.Sort = LogicSort::boolSort(); }

static void setHeapSort(VCExpr &Expr) { Expr.Sort = LogicSort::heap(); }

static std::unique_ptr<VExpr> pointerProvenance(const VExpr *E) {
  while (E && E->K == VExpr::Cast)
    E = static_cast<const VCastExpr *>(E)->Inner.get();
  if (E && E->K == VExpr::BinOp) {
    const auto *B = static_cast<const VBinOpExpr *>(E);
    if ((B->Op == VBinOp::Add || B->Op == VBinOp::Sub) &&
        B->Lhs->Ty.Kind == VTypeKind::Ptr)
      return pointerProvenance(B->Lhs.get());
  }
  if (!E || E->K != VExpr::Var)
    return nullptr;
  const auto *V = static_cast<const VVarExpr *>(E);
  if (V->ProvenanceVariable.empty())
    return nullptr;
  return std::make_unique<VVarExpr>(V->ProvenanceVariable, VType::makePtr(),
                                    V->Loc);
}

static std::unique_ptr<VCExpr> vcTrue() {
  auto Result = std::make_unique<VCExpr>(VCExpr::True);
  setBoolSort(*Result);
  return Result;
}

static std::unique_ptr<VCExpr> vcAnd(std::unique_ptr<VCExpr> A,
                                     std::unique_ptr<VCExpr> B) {
  if (!A)
    return B;
  if (!B)
    return A;
  auto N = std::make_unique<VCExpr>(VCExpr::And);
  setBoolSort(*N);
  N->Loc = A->Loc;
  N->Children.push_back(std::move(A));
  N->Children.push_back(std::move(B));
  return N;
}

static std::unique_ptr<VCExpr> vcNot(std::unique_ptr<VCExpr> E) {
  auto N = std::make_unique<VCExpr>(VCExpr::Not);
  setBoolSort(*N);
  if (E)
    N->Loc = E->Loc;
  N->Children.push_back(std::move(E));
  return N;
}

static std::unique_ptr<VCExpr> vcOr(std::unique_ptr<VCExpr> A,
                                    std::unique_ptr<VCExpr> B) {
  if (!A)
    return B;
  if (!B)
    return A;
  auto N = std::make_unique<VCExpr>(VCExpr::Or);
  setBoolSort(*N);
  N->Loc = A->Loc;
  N->Children.push_back(std::move(A));
  N->Children.push_back(std::move(B));
  return N;
}

static bool containsHeapSelect(const VCExpr *E) {
  if (!E)
    return false;
  if (E->K == VCExpr::Select)
    return true;
  for (const auto &Child : E->Children)
    if (containsHeapSelect(Child.get()))
      return true;
  return false;
}

static std::unique_ptr<VCExpr> cloneVCExpr(const VCExpr *E) {
  if (!E)
    return nullptr;
  auto Copy = std::make_unique<VCExpr>(E->K);
  Copy->Sort = E->Sort;
  Copy->Loc = E->Loc;
  Copy->EndLoc = E->EndLoc;
  Copy->Source = E->Source;
  Copy->IntVal = E->IntVal;
  Copy->BoolVal = E->BoolVal;
  Copy->Name = E->Name;
  Copy->Binder = E->Binder;
  Copy->OverflowOp = E->OverflowOp;
  Copy->SpecCallee = E->SpecCallee;
  for (const auto &Child : E->Children)
    Copy->Children.push_back(cloneVCExpr(Child.get()));
  return Copy;
}

static bool equalLogicExpr(const LogicExpr *Left, const LogicExpr *Right) {
  if (!Left || !Right)
    return Left == Right;
  if (Left->K != Right->K || Left->Sort.Kind != Right->Sort.Kind ||
      Left->Sort.BitWidth != Right->Sort.BitWidth ||
      Left->Sort.Signedness != Right->Sort.Signedness ||
      Left->IntVal != Right->IntVal || Left->BoolVal != Right->BoolVal ||
      Left->Name != Right->Name || Left->Binder != Right->Binder ||
      Left->OverflowOp != Right->OverflowOp ||
      Left->SpecCallee != Right->SpecCallee ||
      Left->Children.size() != Right->Children.size())
    return false;
  for (unsigned I = 0; I != Left->Children.size(); ++I)
    if (!equalLogicExpr(Left->Children[I].get(), Right->Children[I].get()))
      return false;
  return true;
}

static std::unique_ptr<VCExpr>
buildCompleteGoal(const std::vector<Obligation> &Obligations) {
  if (Obligations.empty())
    return vcTrue();
  auto Complete = cloneVCExpr(Obligations.front().Goal.get());
  for (unsigned I = 1; I != Obligations.size(); ++I)
    Complete =
        vcAnd(std::move(Complete), cloneVCExpr(Obligations[I].Goal.get()));
  return Complete;
}

static bool isExactNegation(const LogicExpr *Query, const LogicExpr *Goal) {
  return Query && Query->K == LogicExpr::Not &&
         Query->Sort.Kind == LogicSortKind::Bool &&
         Query->Children.size() == 1 &&
         equalLogicExpr(Query->Children.front().get(), Goal);
}

static bool containsEmbeddedNul(llvm::StringRef Value) {
  return Value.contains('\0');
}

static bool isCanonicalIntegerLiteral(llvm::StringRef Value) {
  constexpr size_t MaxIntegerDigits = 4096;
  if (Value.empty() || Value.size() > MaxIntegerDigits)
    return false;
  size_t I = Value.front() == '-' ? 1 : 0;
  if (I == Value.size())
    return false;
  if (Value[I] == '0')
    return I == 0 && Value.size() == 1;
  if (Value[I] < '1' || Value[I] > '9')
    return false;
  for (++I; I != Value.size(); ++I)
    if (Value[I] < '0' || Value[I] > '9')
      return false;
  return true;
}

static std::unique_ptr<VCExpr> vcBinary(VCExpr::Kind Kind,
                                        std::unique_ptr<VCExpr> L,
                                        std::unique_ptr<VCExpr> R) {
  auto N = std::make_unique<VCExpr>(Kind);
  setBoolSort(*N);
  N->Loc = L->Loc;
  N->Children.push_back(std::move(L));
  N->Children.push_back(std::move(R));
  return N;
}

static std::unique_ptr<VCExpr> mathLimit(unsigned BitWidth, bool IsSigned,
                                         bool Minimum) {
  llvm::APInt Value = Minimum
                          ? (IsSigned ? llvm::APInt::getSignedMinValue(BitWidth)
                                      : llvm::APInt(BitWidth, 0))
                          : (IsSigned ? llvm::APInt::getSignedMaxValue(BitWidth)
                                      : llvm::APInt::getMaxValue(BitWidth));
  llvm::SmallString<64> Buffer;
  Value.toString(Buffer, 10, IsSigned);
  auto N = std::make_unique<VCExpr>(VCExpr::IntLit);
  N->IntVal = std::string(Buffer);
  N->Sort = LogicSort::mathematicalInteger(BitWidth, IsSigned);
  return N;
}

static bool validateLogicSort(const LogicSort &Sort, std::string &Error) {
  if (Sort.Kind == LogicSortKind::Invalid) {
    Error = "invalid sort in obligation IR";
    return false;
  }
  if (Sort.Kind == LogicSortKind::BitVector ||
      Sort.Kind == LogicSortKind::MathematicalInteger) {
    if (Sort.BitWidth == 0) {
      Error = "zero-width bitvector in obligation IR";
      return false;
    }
    if (Sort.BitWidth > MaxLogicIntegerBitWidth) {
      Error = "integer width exceeds the obligation IR limit";
      return false;
    }
  } else if (Sort.BitWidth != 0) {
    Error = "non-integer sort has a bit width in obligation IR";
    return false;
  }
  if (Sort.Kind == LogicSortKind::Bool || Sort.Kind == LogicSortKind::Heap) {
    if (Sort.Signedness != LogicSignedness::None) {
      Error = "non-numeric sort has signedness in obligation IR";
      return false;
    }
  } else if (Sort.Kind == LogicSortKind::Pointer) {
    if (Sort.Signedness != LogicSignedness::Unsigned) {
      Error = "pointer sort is not unsigned in obligation IR";
      return false;
    }
  } else if (Sort.Signedness == LogicSignedness::None) {
    Error = "integer sort lacks signedness in obligation IR";
    return false;
  }
  return true;
}

static bool validateSource(const ObligationSource &Source, std::string &Error) {
  const bool HasStart =
      !Source.File.empty() || Source.Line != 0 || Source.Column != 0;
  const bool HasEnd = Source.EndLine != 0 || Source.EndColumn != 0;
  if (!HasStart) {
    if (!HasEnd)
      return true;
    Error = "source range has an end without a start";
    return false;
  }
  if (Source.File.empty() || Source.Line == 0 || Source.Column == 0) {
    Error = "source range has an incomplete start";
    return false;
  }
  if (!HasEnd)
    return true;
  if (Source.EndLine == 0 || Source.EndColumn == 0) {
    Error = "source range has an incomplete end";
    return false;
  }
  if (Source.EndLine < Source.Line ||
      (Source.EndLine == Source.Line && Source.EndColumn < Source.Column)) {
    Error = "source range end precedes its start";
    return false;
  }
  return true;
}

static bool validateLogicExpr(const LogicExpr *Expr, std::string &Error) {
  if (!Expr) {
    Error = "null term in obligation IR";
    return false;
  }
  if (containsEmbeddedNul(Expr->Source.File)) {
    Error = "embedded NUL in obligation term source";
    return false;
  }
  if (!validateSource(Expr->Source, Error))
    return false;
  if (!validateLogicSort(Expr->Sort, Error))
    return false;
  if (containsEmbeddedNul(Expr->IntVal) || containsEmbeddedNul(Expr->Name) ||
      containsEmbeddedNul(Expr->Binder) ||
      containsEmbeddedNul(Expr->SpecCallee)) {
    Error = "embedded NUL in obligation term";
    return false;
  }
  if ((Expr->K != LogicExpr::IntLit && Expr->IntVal != "0") ||
      (Expr->K != LogicExpr::BoolLit && Expr->BoolVal) ||
      (Expr->K != LogicExpr::Var && !Expr->Name.empty()) ||
      (Expr->K != LogicExpr::Forall && Expr->K != LogicExpr::Exists &&
       !Expr->Binder.empty()) ||
      (Expr->K != LogicExpr::NoOverflow &&
       Expr->OverflowOp != LogicOverflowOp::Add) ||
      (Expr->K != LogicExpr::SpecCall && !Expr->SpecCallee.empty())) {
    Error = "inactive payload is set in obligation term";
    return false;
  }
  for (const auto &Child : Expr->Children)
    if (!validateLogicExpr(Child.get(), Error))
      return false;

  auto requireArity = [&](unsigned Minimum, unsigned Maximum) {
    if (Expr->Children.size() >= Minimum && Expr->Children.size() <= Maximum)
      return true;
    Error = "malformed obligation term: unexpected operand count";
    return false;
  };
  auto sameSort = [](const LogicSort &Left, const LogicSort &Right) {
    if (Left.Kind != Right.Kind)
      return false;
    if (Left.Kind == LogicSortKind::MathematicalInteger)
      return true;
    return Left.BitWidth == Right.BitWidth &&
           Left.Signedness == Right.Signedness;
  };
  auto requireSort = [&](LogicSortKind Kind, const char *Message) {
    if (Expr->Sort.Kind == Kind)
      return true;
    Error = Message;
    return false;
  };
  auto requireChildSort = [&](unsigned Index, LogicSortKind Kind,
                              const char *Message) {
    if (Index < Expr->Children.size() &&
        Expr->Children[Index]->Sort.Kind == Kind)
      return true;
    Error = Message;
    return false;
  };
  auto isArithmeticSort = [](LogicSortKind Kind) {
    return Kind == LogicSortKind::MathematicalInteger ||
           Kind == LogicSortKind::BitVector || Kind == LogicSortKind::Pointer;
  };
  switch (Expr->K) {
  case VCExpr::True:
  case VCExpr::False:
  case VCExpr::BoolLit:
    return requireArity(0, 0) &&
           requireSort(LogicSortKind::Bool,
                       "boolean literal has a non-boolean sort");
  case VCExpr::IntLit:
    if (!requireArity(0, 0))
      return false;
    if (!isCanonicalIntegerLiteral(Expr->IntVal)) {
      Error = "integer literal is not canonical signed decimal";
      return false;
    }
    if (Expr->Sort.Kind == LogicSortKind::MathematicalInteger ||
        Expr->Sort.Kind == LogicSortKind::BitVector ||
        Expr->Sort.Kind == LogicSortKind::Pointer)
      return true;
    Error = "integer literal has a non-numeric sort";
    return false;
  case VCExpr::Var:
    if (Expr->Name.empty()) {
      Error = "logical variable has no identity";
      return false;
    }
    return requireArity(0, 0);
  case VCExpr::Not:
    return requireArity(1, 1) &&
           requireSort(LogicSortKind::Bool,
                       "logical negation has a non-boolean result") &&
           requireChildSort(0, LogicSortKind::Bool,
                            "logical negation has a non-boolean operand");
  case VCExpr::Neg:
    if (!requireArity(1, 1))
      return false;
    if (!sameSort(Expr->Sort, Expr->Children[0]->Sort)) {
      Error = "unary arithmetic changes its operand sort";
      return false;
    }
    if (!isArithmeticSort(Expr->Sort.Kind)) {
      Error = "arithmetic negation has a non-numeric operand";
      return false;
    }
    return true;
  case VCExpr::BitNot:
    if (!requireArity(1, 1) ||
        !requireSort(LogicSortKind::BitVector,
                     "bitwise complement has a non-bitvector result") ||
        !sameSort(Expr->Sort, Expr->Children[0]->Sort)) {
      Error = "bitwise complement changes its operand sort";
      return false;
    }
    return true;
  case VCExpr::ValidPtr:
    return requireArity(1, 1) &&
           requireSort(LogicSortKind::Bool,
                       "pointer-validity predicate has a non-boolean result") &&
           requireChildSort(0, LogicSortKind::Pointer,
                            "pointer-validity predicate has a non-pointer "
                            "operand");
  case VCExpr::IntToBv:
    if (!requireArity(1, 1) ||
        !requireSort(LogicSortKind::BitVector,
                     "int-to-bitvector conversion has a non-bitvector result"))
      return false;
    if (Expr->Children[0]->Sort.Kind != LogicSortKind::MathematicalInteger &&
        Expr->Children[0]->Sort.Kind != LogicSortKind::Pointer) {
      Error = "int-to-bitvector conversion has a non-integer operand";
      return false;
    }
    return true;
  case VCExpr::BvToInt:
    return requireArity(1, 1) &&
           requireSort(
               LogicSortKind::MathematicalInteger,
               "bitvector-to-int conversion has a non-integer result") &&
           requireChildSort(0, LogicSortKind::BitVector,
                            "bitvector-to-int conversion has a non-bitvector "
                            "operand");
  case VCExpr::BvResize:
    return requireArity(1, 1) &&
           requireSort(LogicSortKind::BitVector,
                       "bitvector resize has a non-bitvector result") &&
           requireChildSort(0, LogicSortKind::BitVector,
                            "bitvector resize has a non-bitvector operand");
  case VCExpr::And:
  case VCExpr::Or:
    if (!requireArity(2, 2) ||
        !requireSort(LogicSortKind::Bool,
                     "logical connective has a non-boolean result"))
      return false;
    for (const auto &Child : Expr->Children)
      if (Child->Sort.Kind != LogicSortKind::Bool) {
        Error = "logical connective has a non-boolean operand";
        return false;
      }
    return true;
  case VCExpr::Eq:
  case VCExpr::Ne:
    if (!requireArity(2, 2) ||
        !requireSort(LogicSortKind::Bool, "equality has a non-boolean result"))
      return false;
    if (!sameSort(Expr->Children[0]->Sort, Expr->Children[1]->Sort)) {
      Error = "equality operands have different logic sorts";
      return false;
    }
    return true;
  case VCExpr::Lt:
  case VCExpr::Le:
  case VCExpr::Gt:
  case VCExpr::Ge:
    if (!requireArity(2, 2) ||
        !requireSort(LogicSortKind::Bool,
                     "comparison has a non-boolean result"))
      return false;
    if (!sameSort(Expr->Children[0]->Sort, Expr->Children[1]->Sort)) {
      Error = "comparison operands have different logic sorts";
      return false;
    }
    if (!isArithmeticSort(Expr->Children[0]->Sort.Kind)) {
      Error = "ordered comparison has non-numeric operands";
      return false;
    }
    if (Expr->Children[0]->Sort.Kind == LogicSortKind::BitVector &&
        Expr->Children[0]->Sort.Signedness !=
            Expr->Children[1]->Sort.Signedness) {
      Error = "bitvector comparison operands have different signedness";
      return false;
    }
    return true;
  case VCExpr::Add:
  case VCExpr::Sub:
    if (!requireArity(2, 2))
      return false;
    if (Expr->Sort.Kind == LogicSortKind::Pointer) {
      const LogicSortKind Left = Expr->Children[0]->Sort.Kind;
      const LogicSortKind Right = Expr->Children[1]->Sort.Kind;
      const bool Valid =
          (Left == LogicSortKind::Pointer ||
           Left == LogicSortKind::MathematicalInteger) &&
          (Right == LogicSortKind::Pointer ||
           Right == LogicSortKind::MathematicalInteger) &&
          (Left == LogicSortKind::Pointer || Right == LogicSortKind::Pointer);
      if (!Valid)
        Error = "pointer arithmetic has invalid operand sorts";
      return Valid;
    }
    if (!isArithmeticSort(Expr->Sort.Kind) ||
        !sameSort(Expr->Sort, Expr->Children[0]->Sort) ||
        !sameSort(Expr->Sort, Expr->Children[1]->Sort)) {
      Error = "arithmetic term " +
              std::to_string(static_cast<unsigned>(Expr->K)) +
              " has result sort " + logicSortName(Expr->Sort.Kind) +
              ", left sort " + logicSortName(Expr->Children[0]->Sort.Kind) +
              ", and right sort " + logicSortName(Expr->Children[1]->Sort.Kind);
      return false;
    }
    return true;
  case VCExpr::Mul:
  case VCExpr::Div:
  case VCExpr::Rem:
    if (!requireArity(2, 2) || !isArithmeticSort(Expr->Sort.Kind) ||
        !sameSort(Expr->Sort, Expr->Children[0]->Sort) ||
        !sameSort(Expr->Sort, Expr->Children[1]->Sort)) {
      Error = "arithmetic term " +
              std::to_string(static_cast<unsigned>(Expr->K)) +
              " has result sort " + logicSortName(Expr->Sort.Kind) +
              ", left sort " + logicSortName(Expr->Children[0]->Sort.Kind) +
              ", and right sort " + logicSortName(Expr->Children[1]->Sort.Kind);
      return false;
    }
    return true;
  case VCExpr::BitAnd:
  case VCExpr::BitOr:
  case VCExpr::BitXor:
    if (!requireArity(2, 2) || Expr->Sort.Kind != LogicSortKind::BitVector ||
        !sameSort(Expr->Sort, Expr->Children[0]->Sort) ||
        !sameSort(Expr->Sort, Expr->Children[1]->Sort)) {
      Error = "bitwise term has inconsistent bitvector sorts";
      return false;
    }
    return true;
  case VCExpr::Shl:
  case VCExpr::Shr:
    if (!requireArity(2, 2) || Expr->Sort.Kind != LogicSortKind::BitVector ||
        !sameSort(Expr->Sort, Expr->Children[0]->Sort) ||
        Expr->Children[1]->Sort.Kind != LogicSortKind::BitVector ||
        Expr->Children[1]->Sort.BitWidth != Expr->Sort.BitWidth) {
      Error = "shift term has inconsistent bitvector sorts";
      return false;
    }
    return true;
  case VCExpr::Ite:
    if (!requireArity(3, 3) ||
        !requireChildSort(0, LogicSortKind::Bool,
                          "conditional has a non-boolean condition"))
      return false;
    if (!sameSort(Expr->Sort, Expr->Children[1]->Sort) ||
        !sameSort(Expr->Sort, Expr->Children[2]->Sort)) {
      Error = "conditional branches and result have different logic sorts";
      return false;
    }
    return true;
  case VCExpr::Select:
    return requireArity(2, 2) &&
           requireChildSort(0, LogicSortKind::Heap,
                            "heap selection has a non-heap operand") &&
           requireChildSort(1, LogicSortKind::Pointer,
                            "heap selection has a non-pointer address") &&
           Expr->Sort.Kind != LogicSortKind::Heap;
  case VCExpr::Store:
    return requireArity(4, 4) &&
           requireSort(LogicSortKind::Bool,
                       "heap store relation has a non-boolean result") &&
           requireChildSort(0, LogicSortKind::Heap,
                            "heap store has a non-heap input") &&
           requireChildSort(1, LogicSortKind::Pointer,
                            "heap store has a non-pointer address") &&
           Expr->Children[2]->Sort.Kind != LogicSortKind::Heap &&
           requireChildSort(3, LogicSortKind::Heap,
                            "heap store has a non-heap output");
  case VCExpr::Forall:
  case VCExpr::Exists:
    if (Expr->Binder.empty()) {
      Error = "quantifier has no binder identity";
      return false;
    }
    return requireArity(3, 3) &&
           requireSort(LogicSortKind::Bool,
                       "quantifier has a non-boolean result") &&
           requireChildSort(0, LogicSortKind::MathematicalInteger,
                            "quantifier has a non-integer lower bound") &&
           requireChildSort(1, LogicSortKind::MathematicalInteger,
                            "quantifier has a non-integer upper bound") &&
           requireChildSort(2, LogicSortKind::Bool,
                            "quantifier has a non-boolean body");
  case VCExpr::NoOverflow:
    if (!requireArity(1, 2) ||
        !requireSort(LogicSortKind::Bool,
                     "overflow predicate has a non-boolean result"))
      return false;
    if ((Expr->OverflowOp == LogicOverflowOp::Neg) !=
        (Expr->Children.size() == 1)) {
      Error = "overflow predicate has the wrong operand count";
      return false;
    }
    for (const auto &Child : Expr->Children)
      if (Child->Sort.Kind != LogicSortKind::BitVector) {
        Error = "overflow predicate has a non-bitvector operand";
        return false;
      }
    return true;
  case VCExpr::SpecCall:
    if (Expr->SpecCallee.empty()) {
      Error = "spec application has no callee identity";
      return false;
    }
    return true;
  }
  Error = "unknown obligation term kind";
  return false;
}

static void collectQuantifierBinders(const LogicExpr *Expr,
                                     std::set<std::string> &Binders) {
  if (!Expr)
    return;
  if (Expr->K == LogicExpr::Forall || Expr->K == LogicExpr::Exists)
    Binders.insert(Expr->Binder);
  for (const auto &Child : Expr->Children)
    collectQuantifierBinders(Child.get(), Binders);
}

static bool equivalentVariableSort(const LogicSort &Left,
                                   const LogicSort &Right) {
  if (Left.Kind != Right.Kind)
    return false;
  if (Left.Kind == LogicSortKind::MathematicalInteger)
    return true;
  return Left.BitWidth == Right.BitWidth && Left.Signedness == Right.Signedness;
}

static bool validateVariableScopes(
    const LogicExpr *Expr, const std::set<std::string> &AllBinders,
    std::set<std::string> Bound,
    std::map<std::string, LogicSort> &FreeVariables, std::string &Error) {
  if (!Expr)
    return false;
  if ((Expr->K == LogicExpr::Forall || Expr->K == LogicExpr::Exists))
    Bound.insert(Expr->Binder);
  if (Expr->K == LogicExpr::Var) {
    if (Bound.count(Expr->Name)) {
      if (Expr->Sort.Kind != LogicSortKind::MathematicalInteger) {
        Error = "quantifier binder occurrence is not a mathematical integer";
        return false;
      }
    } else {
      if (AllBinders.count(Expr->Name)) {
        Error = "quantifier binder collides with a free variable";
        return false;
      }
      auto [It, Inserted] = FreeVariables.emplace(Expr->Name, Expr->Sort);
      if (!Inserted && !equivalentVariableSort(It->second, Expr->Sort)) {
        Error = "logical variable has inconsistent sorts: " + Expr->Name;
        return false;
      }
    }
  }
  for (const auto &Child : Expr->Children)
    if (!validateVariableScopes(Child.get(), AllBinders, Bound, FreeVariables,
                                Error))
      return false;
  return true;
}

static bool validateVariableScopes(const LogicExpr *Expr, std::string &Error) {
  std::set<std::string> Binders;
  collectQuantifierBinders(Expr, Binders);
  std::map<std::string, LogicSort> FreeVariables;
  return validateVariableScopes(Expr, Binders, {}, FreeVariables, Error);
}

static bool
validateVariableScopes(const LogicExpr *Expr,
                       std::map<std::string, LogicSort> &FreeVariables,
                       std::string &Error) {
  std::set<std::string> Binders;
  collectQuantifierBinders(Expr, Binders);
  return validateVariableScopes(Expr, Binders, {}, FreeVariables, Error);
}

static bool canCoerceLogicSort(const LogicSort &Source,
                               const LogicSort &Target) {
  if (Source.Kind == Target.Kind)
    return Source.Kind != LogicSortKind::BitVector ||
           (Source.BitWidth == Target.BitWidth &&
            Source.Signedness == Target.Signedness);
  return (Source.Kind == LogicSortKind::MathematicalInteger &&
          Target.Kind == LogicSortKind::BitVector) ||
         (Source.Kind == LogicSortKind::BitVector &&
          Target.Kind == LogicSortKind::MathematicalInteger);
}

static bool
validateLogicCalls(const LogicExpr *Expr,
                   const std::map<std::string, LogicFunctionDecl> &Functions,
                   std::string &Error) {
  if (!Expr)
    return false;
  for (const auto &Child : Expr->Children)
    if (!validateLogicCalls(Child.get(), Functions, Error))
      return false;
  if (Expr->K != LogicExpr::SpecCall)
    return true;
  auto It = Functions.find(Expr->SpecCallee);
  if (It == Functions.end()) {
    Error = "logical application has no owned declaration: " + Expr->SpecCallee;
    return false;
  }
  const LogicFunctionDecl &Function = It->second;
  if (Expr->Children.size() != Function.Parameters.size()) {
    Error = "logical application argument count mismatch: " + Expr->SpecCallee;
    return false;
  }
  for (unsigned I = 0; I < Expr->Children.size(); ++I)
    if (!canCoerceLogicSort(Expr->Children[I]->Sort,
                            Function.Parameters[I].Sort)) {
      Error = "logical application argument sort mismatch: " + Expr->SpecCallee;
      return false;
    }
  if (!canCoerceLogicSort(Function.ResultSort, Expr->Sort)) {
    Error = "logical application result sort mismatch: " + Expr->SpecCallee;
    return false;
  }
  return true;
}

static bool
validateDefinitionVariables(const LogicExpr *Expr,
                            const std::map<std::string, LogicSort> &Parameters,
                            std::set<std::string> Bound, std::string &Error) {
  if (!Expr)
    return false;
  if (Expr->K == LogicExpr::Var && !Bound.count(Expr->Name)) {
    auto It = Parameters.find(Expr->Name);
    if (It == Parameters.end()) {
      Error = "logical function definition has a free variable: " + Expr->Name;
      return false;
    }
    if (It->second.Kind != Expr->Sort.Kind ||
        (It->second.Kind != LogicSortKind::MathematicalInteger &&
         (It->second.BitWidth != Expr->Sort.BitWidth ||
          It->second.Signedness != Expr->Sort.Signedness))) {
      Error = "logical function parameter sort mismatch: " + Expr->Name;
      return false;
    }
  }
  if (Expr->K == LogicExpr::Forall || Expr->K == LogicExpr::Exists)
    Bound.insert(Expr->Binder);
  for (const auto &Child : Expr->Children)
    if (!validateDefinitionVariables(Child.get(), Parameters, Bound, Error))
      return false;
  return true;
}

static void collectRequiredFeatures(const LogicExpr *Expr,
                                    LogicFeatureSet &Features) {
  if (!Expr)
    return;
  switch (Expr->Sort.Kind) {
  case LogicSortKind::MathematicalInteger:
    Features |= logicFeature(LogicFeature::MathematicalIntegers);
    break;
  case LogicSortKind::BitVector:
    Features |= logicFeature(LogicFeature::BitVectors);
    break;
  case LogicSortKind::Pointer:
    Features |= logicFeature(LogicFeature::MathematicalIntegers) |
                logicFeature(LogicFeature::Pointers);
    break;
  case LogicSortKind::Heap:
    Features |= logicFeature(LogicFeature::MathematicalIntegers) |
                logicFeature(LogicFeature::HeapArrays);
    break;
  case LogicSortKind::Invalid:
  case LogicSortKind::Bool:
    break;
  }
  if (Expr->K == VCExpr::Select || Expr->K == VCExpr::Store)
    Features |= logicFeature(LogicFeature::HeapArrays);
  if (Expr->K == VCExpr::Forall || Expr->K == VCExpr::Exists)
    Features |= logicFeature(LogicFeature::Quantifiers);
  if (Expr->K == VCExpr::SpecCall)
    Features |= logicFeature(LogicFeature::SpecFunctions);
  for (const auto &Child : Expr->Children)
    collectRequiredFeatures(Child.get(), Features);
}

class ObligationBuilder {
  std::string ResultVarName;
  std::string CurHeap;
  std::map<std::string, std::string> BoundVars;
  std::map<std::string, VIntMode> BoundVarModes;
  std::set<std::string> HeapVariables;
  unsigned QuantifierCounter = 0;
  std::string ConstructionError;

  std::unique_ptr<VCExpr> fail(std::string Message) {
    if (ConstructionError.empty())
      ConstructionError = std::move(Message);
    return std::make_unique<VCExpr>(VCExpr::False);
  }

  static VIntMode intModeOf(const VCExpr *E) {
    if (!E)
      return VIntMode::Machine;
    return E->Sort.Kind == LogicSortKind::BitVector ? VIntMode::Machine
                                                    : VIntMode::Math;
  }

  static VIntMode intModeOfVType(const VType &Ty) {
    if (Ty.Kind == VTypeKind::Int32 || Ty.Kind == VTypeKind::Int64)
      return Ty.IntMode;
    return VIntMode::Machine;
  }

  bool isActiveBoundVariable(const VCExpr *Expr) const {
    if (!Expr || Expr->K != VCExpr::Var)
      return false;
    return std::any_of(
        BoundVars.begin(), BoundVars.end(),
        [&](const auto &Entry) { return Entry.second == Expr->Name; });
  }

  std::unique_ptr<VCExpr> toMachineSort(std::unique_ptr<VCExpr> E,
                                        const LogicSort &TargetSort) {
    if (!E)
      return E;
    if (E->K == VCExpr::BvToInt && E->Children.size() == 1 && E->Children[0] &&
        E->Children[0]->Sort.Kind == LogicSortKind::BitVector)
      E = std::move(E->Children[0]);
    if (E->Sort.Kind == LogicSortKind::BitVector) {
      if (E->Sort.BitWidth == TargetSort.BitWidth &&
          E->Sort.Signedness == TargetSort.Signedness)
        return E;
      auto Resize = std::make_unique<VCExpr>(VCExpr::BvResize);
      Resize->Sort = TargetSort;
      Resize->Loc = E->Loc;
      Resize->Children.push_back(std::move(E));
      return Resize;
    }
    auto Converted = std::make_unique<VCExpr>(VCExpr::IntToBv);
    Converted->Sort = TargetSort;
    Converted->Loc = E->Loc;
    Converted->Children.push_back(std::move(E));
    return Converted;
  }

  std::unique_ptr<VCExpr> toMode(std::unique_ptr<VCExpr> E, VIntMode Target) {
    if (!E)
      return E;
    if (E->Sort.Kind == LogicSortKind::Pointer)
      return E;
    if (intModeOf(E.get()) == Target)
      return E;
    if (Target == VIntMode::Math && E->K == VCExpr::IntToBv &&
        E->Children.size() == 1 && isActiveBoundVariable(E->Children[0].get()))
      return std::move(E->Children[0]);
    if (Target == VIntMode::Machine) {
      const LogicSort TargetSort =
          LogicSort::bitVector(E->Sort.BitWidth ? E->Sort.BitWidth : 32,
                               E->Sort.Signedness != LogicSignedness::Unsigned);
      switch (E->K) {
      case VCExpr::Add:
      case VCExpr::Sub:
      case VCExpr::Mul:
        E->Children[0] = toMachineSort(std::move(E->Children[0]), TargetSort);
        E->Children[1] = toMachineSort(std::move(E->Children[1]), TargetSort);
        E->Sort = TargetSort;
        return E;
      case VCExpr::Neg:
        E->Children[0] = toMachineSort(std::move(E->Children[0]), TargetSort);
        E->Sort = TargetSort;
        return E;
      case VCExpr::Ite:
        E->Children[1] = toMachineSort(std::move(E->Children[1]), TargetSort);
        E->Children[2] = toMachineSort(std::move(E->Children[2]), TargetSort);
        E->Sort = TargetSort;
        return E;
      default:
        return toMachineSort(std::move(E), TargetSort);
      }
    }
    auto N = std::make_unique<VCExpr>(
        Target == VIntMode::Machine ? VCExpr::IntToBv : VCExpr::BvToInt);
    N->Loc = E->Loc;
    N->Sort = Target == VIntMode::Machine
                  ? LogicSort::bitVector(
                        E->Sort.BitWidth ? E->Sort.BitWidth : 32,
                        E->Sort.Signedness != LogicSignedness::Unsigned)
                  : LogicSort::mathematicalInteger(
                        E->Sort.BitWidth ? E->Sort.BitWidth : 32,
                        E->Sort.Signedness != LogicSignedness::Unsigned);
    N->Children.push_back(std::move(E));
    return N;
  }

  std::pair<std::unique_ptr<VCExpr>, std::unique_ptr<VCExpr>>
  unifyIntModes(std::unique_ptr<VCExpr> L, std::unique_ptr<VCExpr> R) {
    VIntMode M = intModeOf(L.get());
    if (intModeOf(R.get()) == VIntMode::Math)
      M = VIntMode::Math;
    return {toMode(std::move(L), M), toMode(std::move(R), M)};
  }

  std::unique_ptr<VCExpr>
  exactCrossModeEquality(VCExpr::Kind Kind, std::unique_ptr<VCExpr> Machine,
                         std::unique_ptr<VCExpr> Math) {
    const unsigned BitWidth = Machine->Sort.BitWidth;
    const bool IsSigned = Machine->Sort.Signedness == LogicSignedness::Signed;
    auto InRange = vcAnd(vcBinary(VCExpr::Ge, cloneVCExpr(Math.get()),
                                  mathLimit(BitWidth, IsSigned, true)),
                         vcBinary(VCExpr::Le, cloneVCExpr(Math.get()),
                                  mathLimit(BitWidth, IsSigned, false)));

    auto Converted = toMode(std::move(Math), VIntMode::Machine);
    if (Converted->Sort.BitWidth != BitWidth) {
      auto Resize = std::make_unique<VCExpr>(VCExpr::BvResize);
      Resize->Sort = LogicSort::bitVector(BitWidth, IsSigned);
      Resize->Loc = Converted->Loc;
      Resize->Children.push_back(std::move(Converted));
      Converted = std::move(Resize);
    }

    auto Exact =
        vcAnd(std::move(InRange),
              vcBinary(VCExpr::Eq, std::move(Machine), std::move(Converted)));
    if (Kind == VCExpr::Eq)
      return Exact;
    return vcNot(std::move(Exact));
  }

  std::unique_ptr<VCExpr> fromBin(VBinOp Op, std::unique_ptr<VCExpr> L,
                                  std::unique_ptr<VCExpr> R) {
    VCExpr::Kind K = VCExpr::Eq;
    switch (Op) {
    case VBinOp::Add:
      K = VCExpr::Add;
      break;
    case VBinOp::Sub:
      K = VCExpr::Sub;
      break;
    case VBinOp::Mul:
      K = VCExpr::Mul;
      break;
    case VBinOp::Div:
      K = VCExpr::Div;
      break;
    case VBinOp::Rem:
      K = VCExpr::Rem;
      break;
    case VBinOp::BitAnd:
      K = VCExpr::BitAnd;
      break;
    case VBinOp::BitOr:
      K = VCExpr::BitOr;
      break;
    case VBinOp::BitXor:
      K = VCExpr::BitXor;
      break;
    case VBinOp::Shl:
      K = VCExpr::Shl;
      break;
    case VBinOp::Shr:
      K = VCExpr::Shr;
      break;
    case VBinOp::Lt:
      K = VCExpr::Lt;
      break;
    case VBinOp::Le:
      K = VCExpr::Le;
      break;
    case VBinOp::Gt:
      K = VCExpr::Gt;
      break;
    case VBinOp::Ge:
      K = VCExpr::Ge;
      break;
    case VBinOp::Eq:
      K = VCExpr::Eq;
      break;
    case VBinOp::Ne:
      K = VCExpr::Ne;
      break;
    case VBinOp::And:
      K = VCExpr::And;
      break;
    case VBinOp::Or:
      K = VCExpr::Or;
      break;
    }
    const bool HasHeap = L->Sort.Kind == LogicSortKind::Heap ||
                         R->Sort.Kind == LogicSortKind::Heap;
    if (HasHeap) {
      if ((K != VCExpr::Eq && K != VCExpr::Ne) ||
          L->Sort.Kind != LogicSortKind::Heap ||
          R->Sort.Kind != LogicSortKind::Heap)
        return fail("unsupported operation involving a heap value");
      auto N = std::make_unique<VCExpr>(K);
      setBoolSort(*N);
      N->Loc = L->Loc;
      N->Children.push_back(std::move(L));
      N->Children.push_back(std::move(R));
      return N;
    }

    bool HasPointer = L->Sort.Kind == LogicSortKind::Pointer ||
                      R->Sort.Kind == LogicSortKind::Pointer;
    bool HasBoolean = L->Sort.Kind == LogicSortKind::Bool ||
                      R->Sort.Kind == LogicSortKind::Bool;
    if ((K == VCExpr::Eq || K == VCExpr::Ne) && !HasPointer && !HasBoolean &&
        L->Sort.Kind != R->Sort.Kind) {
      if (L->Sort.Kind == LogicSortKind::BitVector)
        return exactCrossModeEquality(K, std::move(L), std::move(R));
      return exactCrossModeEquality(K, std::move(R), std::move(L));
    }
    std::pair<std::unique_ptr<VCExpr>, std::unique_ptr<VCExpr>> Unified;
    if (K == VCExpr::Shl || K == VCExpr::Shr) {
      L = toMode(std::move(L), VIntMode::Machine);
      R = toMode(std::move(R), VIntMode::Machine);
      if (R->Sort.BitWidth != L->Sort.BitWidth) {
        auto Resize = std::make_unique<VCExpr>(VCExpr::BvResize);
        Resize->Sort = LogicSort::bitVector(
            L->Sort.BitWidth, R->Sort.Signedness == LogicSignedness::Signed);
        Resize->Loc = R->Loc;
        Resize->Children.push_back(std::move(R));
        R = std::move(Resize);
      }
      Unified = std::make_pair(std::move(L), std::move(R));
    } else {
      Unified = HasPointer
                    ? std::make_pair(toMode(std::move(L), VIntMode::Math),
                                     toMode(std::move(R), VIntMode::Math))
                : HasBoolean ? std::make_pair(std::move(L), std::move(R))
                             : unifyIntModes(std::move(L), std::move(R));
    }
    auto N = std::make_unique<VCExpr>(K);
    if (K == VCExpr::Eq || K == VCExpr::Ne || K == VCExpr::Lt ||
        K == VCExpr::Le || K == VCExpr::Gt || K == VCExpr::Ge ||
        K == VCExpr::And || K == VCExpr::Or)
      N->Sort = LogicSort::boolSort();
    else
      N->Sort = Unified.first->Sort;
    N->Loc = Unified.first->Loc;
    N->Children.push_back(std::move(Unified.first));
    N->Children.push_back(std::move(Unified.second));
    return N;
  }

  std::unique_ptr<VCExpr> fromQuant(const VQuantifiedExpr *Q, bool IsForall) {
    auto N =
        std::make_unique<VCExpr>(IsForall ? VCExpr::Forall : VCExpr::Exists);
    setBoolSort(*N);
    N->Loc = Q->Loc;
    N->Binder =
        "__quant_" + std::to_string(QuantifierCounter++) + "_" + Q->Binder;
    N->Children.push_back(toMode(fromVExpr(Q->Lo.get()), VIntMode::Math));
    N->Children.push_back(toMode(fromVExpr(Q->Hi.get()), VIntMode::Math));
    // Quantified machine integers range over the corresponding mathematical
    // interval and are converted back to their bit-vector type at machine
    // operations. This is equivalent within the typed bounds and keeps array
    // indices in Z3's native integer sort instead of mixing quantified
    // bit-vectors with integer-addressed heaps.

    auto Previous = BoundVars.find(Q->Binder);
    std::string PreviousName;
    bool HadPrevious = Previous != BoundVars.end();
    if (HadPrevious)
      PreviousName = Previous->second;
    auto PreviousMode = BoundVarModes.find(Q->Binder);
    bool HadPreviousMode = PreviousMode != BoundVarModes.end();
    VIntMode SavedMode =
        HadPreviousMode ? PreviousMode->second : VIntMode::Machine;
    BoundVars[Q->Binder] = N->Binder;
    BoundVarModes[Q->Binder] = VIntMode::Machine;
    auto Body = fromVExpr(Q->Body.get());
    if (!containsHeapSelect(Body.get())) {
      BoundVarModes[Q->Binder] = VIntMode::Math;
      Body = fromVExpr(Q->Body.get());
    }
    N->Children.push_back(std::move(Body));
    if (HadPrevious)
      BoundVars[Q->Binder] = std::move(PreviousName);
    else
      BoundVars.erase(Q->Binder);
    if (HadPreviousMode)
      BoundVarModes[Q->Binder] = SavedMode;
    else
      BoundVarModes.erase(Q->Binder);
    return N;
  }

  VIntMode CallerIntMode = VIntMode::Machine;
  bool ForceCallerIntMode = false;

public:
  ObligationBuilder(std::string ResultVar, std::string Heap,
                    VIntMode CallerMode,
                    std::set<std::string> HeapVariables = {},
                    bool ForceCallerMode = false)
      : ResultVarName(std::move(ResultVar)), CurHeap(std::move(Heap)),
        HeapVariables(std::move(HeapVariables)), CallerIntMode(CallerMode),
        ForceCallerIntMode(ForceCallerMode) {}

  std::unique_ptr<VCExpr> fromVExpr(const VExpr *E) {
    auto Result = fromVExprImpl(E);
    if (Result && E)
      Result->EndLoc = E->EndLoc;
    return Result;
  }

  std::unique_ptr<VCExpr> fromVExprImpl(const VExpr *E) {
    if (!E)
      return fail("null VCR expression in obligation lowering");
    switch (E->K) {
    case VExpr::Literal: {
      const auto *L = static_cast<const VLiteralExpr *>(E);
      if (L->Ty.Kind == VTypeKind::Bool) {
        auto N = std::make_unique<VCExpr>(VCExpr::BoolLit);
        N->BoolVal = L->Value != "0";
        N->Loc = L->Loc;
        setBoolSort(*N);
        return N;
      }
      auto N = std::make_unique<VCExpr>(VCExpr::IntLit);
      N->IntVal = L->Value;
      N->Loc = L->Loc;
      N->Sort = logicSortFor(L->Ty.Kind,
                             ForceCallerIntMode ? CallerIntMode
                                                : intModeOfVType(L->Ty),
                             L->Ty.BitWidth, L->Ty.IsSigned);
      return N;
    }
    case VExpr::Var: {
      auto N = std::make_unique<VCExpr>(VCExpr::Var);
      const auto *Variable = static_cast<const VVarExpr *>(E);
      const std::string &Name = Variable->Name;
      auto Bound = BoundVars.find(Name);
      N->Name = Bound == BoundVars.end() ? Name : Bound->second;
      N->Loc = E->Loc;
      if (Bound != BoundVars.end()) {
        N->Sort = LogicSort::mathematicalInteger(Variable->Ty.BitWidth,
                                                 Variable->Ty.IsSigned);
        if (BoundVarModes.at(Name) == VIntMode::Machine)
          return toMode(std::move(N), VIntMode::Machine);
      } else if (HeapVariables.count(N->Name)) {
        setHeapSort(*N);
      } else {
        N->Sort = logicSortFor(
            Variable->Ty.Kind,
            ForceCallerIntMode ? CallerIntMode : intModeOfVType(Variable->Ty),
            Variable->Ty.BitWidth, Variable->Ty.IsSigned);
      }
      return N;
    }
    case VExpr::BinOp: {
      const auto *B = static_cast<const VBinOpExpr *>(E);
      auto N = fromBin(B->Op, fromVExpr(B->Lhs.get()), fromVExpr(B->Rhs.get()));
      N->Loc = B->Loc;
      return N;
    }
    case VExpr::UnaryOp: {
      const auto *U = static_cast<const VUnaryOpExpr *>(E);
      if (U->Op == VUnaryOp::Neg) {
        auto N = std::make_unique<VCExpr>(VCExpr::Neg);
        N->Children.push_back(fromVExpr(U->Operand.get()));
        N->Sort = N->Children[0]->Sort;
        N->Loc = U->Loc;
        return N;
      }
      if (U->Op == VUnaryOp::BitNot) {
        auto N = std::make_unique<VCExpr>(VCExpr::BitNot);
        N->Children.push_back(fromVExpr(U->Operand.get()));
        N->Sort = N->Children[0]->Sort;
        N->Loc = U->Loc;
        return N;
      }
      if (U->Op == VUnaryOp::ValidPtr) {
        if (!U->AllocationHeapVar.empty() && !U->LivenessHeapVar.empty()) {
          auto Owner = std::make_unique<VLoadExpr>(cloneVExpr(U->Operand.get()),
                                                   VType::makePtr(), U->Loc,
                                                   U->AllocationHeapVar);
          std::unique_ptr<VExpr> HasOwner;
          auto Provenance = pointerProvenance(U->Operand.get());
          std::unique_ptr<VExpr> NonzeroProvenance;
          if (Provenance) {
            NonzeroProvenance = std::make_unique<VBinOpExpr>(
                VBinOp::Ne, cloneVExpr(Provenance.get()),
                std::make_unique<VLiteralExpr>(0, VType::makePtr(), U->Loc),
                VType::makeBool(), U->Loc);
            HasOwner = std::make_unique<VBinOpExpr>(
                VBinOp::Eq, cloneVExpr(Owner.get()), std::move(Provenance),
                VType::makeBool(), U->Loc);
          } else {
            HasOwner = std::make_unique<VBinOpExpr>(
                VBinOp::Ne, cloneVExpr(Owner.get()),
                std::make_unique<VLiteralExpr>(0, VType::makePtr(), U->Loc),
                VType::makeBool(), U->Loc);
          }
          auto Live = std::make_unique<VLoadExpr>(
              std::move(Owner), VType::makeBool(), U->Loc, U->LivenessHeapVar);
          auto Valid = std::make_unique<VBinOpExpr>(
              VBinOp::And, std::move(HasOwner), std::move(Live),
              VType::makeBool(), U->Loc);
          if (NonzeroProvenance)
            Valid = std::make_unique<VBinOpExpr>(
                VBinOp::And, std::move(NonzeroProvenance), std::move(Valid),
                VType::makeBool(), U->Loc);
          return fromVExpr(Valid.get());
        }
        auto N = std::make_unique<VCExpr>(VCExpr::ValidPtr);
        N->Children.push_back(fromVExpr(U->Operand.get()));
        N->Loc = U->Loc;
        setBoolSort(*N);
        return N;
      }
      if (U->Op == VUnaryOp::InitializedPtr) {
        if (U->InitializationHeapVar.empty()) {
          auto N = std::make_unique<VCExpr>(VCExpr::BoolLit);
          N->BoolVal = false;
          N->Loc = U->Loc;
          setBoolSort(*N);
          return N;
        }
        VLoadExpr Initialized(cloneVExpr(U->Operand.get()), VType::makeBool(),
                              U->Loc, U->InitializationHeapVar);
        return fromVExpr(&Initialized);
      }
      return vcNot(fromVExpr(U->Operand.get()));
    }
    case VExpr::Conditional: {
      const auto *C = static_cast<const VConditionalExpr *>(E);
      auto N = std::make_unique<VCExpr>(VCExpr::Ite);
      N->Children.push_back(fromVExpr(C->Cond.get()));
      N->Children.push_back(fromVExpr(C->Then.get()));
      N->Children.push_back(fromVExpr(C->Else.get()));
      N->Loc = C->Loc;
      if (N->Children[1]->Sort.Kind == LogicSortKind::Heap &&
          N->Children[2]->Sort.Kind == LogicSortKind::Heap)
        setHeapSort(*N);
      else
        N->Sort = N->Children[1]->Sort;
      return N;
    }
    case VExpr::Result: {
      auto N = std::make_unique<VCExpr>(VCExpr::Var);
      N->Name = ResultVarName.empty() ? "__result_0" : ResultVarName;
      N->Loc = E->Loc;
      N->Sort = logicSortFor(E->Ty.Kind, intModeOfVType(E->Ty), E->Ty.BitWidth,
                             E->Ty.IsSigned);
      return N;
    }
    case VExpr::Old:
      return fromVExpr(static_cast<const VOldExpr *>(E)->Inner.get());
    case VExpr::Cast: {
      const auto *C = static_cast<const VCastExpr *>(E);
      auto Inner = fromVExpr(C->Inner.get());
      if (!Inner)
        return nullptr;
      if (C->Ty.Kind == VTypeKind::Bool && C->FromTy.Kind != VTypeKind::Bool) {
        auto Zero = std::make_unique<VCExpr>(VCExpr::IntLit);
        Zero->Sort = logicSortFor(C->FromTy.Kind, intModeOfVType(C->FromTy),
                                  C->FromTy.BitWidth, C->FromTy.IsSigned);
        Zero->Loc = C->Loc;
        auto N = std::make_unique<VCExpr>(VCExpr::Ne);
        setBoolSort(*N);
        N->Loc = C->Loc;
        N->Children.push_back(std::move(Inner));
        N->Children.push_back(std::move(Zero));
        return N;
      }
      if (C->FromTy.Kind == VTypeKind::Bool && C->Ty.Kind != VTypeKind::Bool) {
        auto One = std::make_unique<VCExpr>(VCExpr::IntLit);
        One->IntVal = "1";
        One->Sort = logicSortFor(C->Ty.Kind, intModeOfVType(C->Ty),
                                 C->Ty.BitWidth, C->Ty.IsSigned);
        One->Loc = C->Loc;
        auto Zero = std::make_unique<VCExpr>(VCExpr::IntLit);
        Zero->Sort = One->Sort;
        Zero->Loc = C->Loc;
        auto N = std::make_unique<VCExpr>(VCExpr::Ite);
        N->Sort = One->Sort;
        N->Loc = C->Loc;
        N->Children.push_back(std::move(Inner));
        N->Children.push_back(std::move(One));
        N->Children.push_back(std::move(Zero));
        return N;
      }
      if (C->FromTy.Kind == VTypeKind::Ptr &&
          (C->Ty.Kind == VTypeKind::Int32 || C->Ty.Kind == VTypeKind::Int64)) {
        if (C->Ty.IntMode == VIntMode::Machine) {
          auto N = std::make_unique<VCExpr>(VCExpr::IntToBv);
          N->Sort = LogicSort::bitVector(C->Ty.BitWidth, C->Ty.IsSigned);
          N->Loc = C->Loc;
          N->Children.push_back(std::move(Inner));
          return N;
        }
        Inner->Sort =
            LogicSort::mathematicalInteger(C->Ty.BitWidth, C->Ty.IsSigned);
        Inner->Loc = C->Loc;
        return Inner;
      }
      VIntMode TargetMode = intModeOfVType(C->Ty);
      Inner = toMode(std::move(Inner), TargetMode);
      const LogicSort TargetSort =
          logicSortFor(C->Ty.Kind, TargetMode, C->Ty.BitWidth, C->Ty.IsSigned);
      if (TargetMode == VIntMode::Machine &&
          (Inner->Sort.BitWidth != C->Ty.BitWidth ||
           Inner->Sort.Signedness != TargetSort.Signedness)) {
        auto Resize = std::make_unique<VCExpr>(VCExpr::BvResize);
        Resize->Sort = TargetSort;
        Resize->Loc = C->Loc;
        Resize->Children.push_back(std::move(Inner));
        Inner = std::move(Resize);
      }
      Inner->Sort = TargetSort;
      Inner->Loc = C->Loc;
      return Inner;
    }
    case VExpr::Load: {
      const auto *L = static_cast<const VLoadExpr *>(E);
      std::string Heap = L->HeapVar.empty() ? CurHeap : L->HeapVar;
      auto N = std::make_unique<VCExpr>(VCExpr::Select);
      N->Sort = logicSortFor(L->Ty.Kind, CallerIntMode, L->Ty.BitWidth,
                             L->Ty.IsSigned);
      N->Loc = L->Loc;
      auto H = std::make_unique<VCExpr>(VCExpr::Var);
      H->Name = Heap;
      H->Loc = L->Loc;
      setHeapSort(*H);
      N->Children.push_back(std::move(H));
      N->Children.push_back(fromVExpr(L->Ptr.get()));
      return N;
    }
    case VExpr::Forall:
      return fromQuant(static_cast<const VQuantifiedExpr *>(E), true);
    case VExpr::Exists:
      return fromQuant(static_cast<const VQuantifiedExpr *>(E), false);
    case VExpr::HeapStore: {
      const auto *H = static_cast<const VHeapStoreExpr *>(E);
      auto N = std::make_unique<VCExpr>(VCExpr::Store);
      N->Loc = H->Loc;
      setBoolSort(*N);
      auto Before = std::make_unique<VCExpr>(VCExpr::Var);
      Before->Name = H->HeapBefore;
      Before->Loc = H->Loc;
      setHeapSort(*Before);
      auto After = std::make_unique<VCExpr>(VCExpr::Var);
      After->Name = H->HeapAfter;
      After->Loc = H->Loc;
      setHeapSort(*After);
      N->Children.push_back(std::move(Before));
      N->Children.push_back(fromVExpr(H->Ptr.get()));
      N->Children.push_back(fromVExpr(H->Val.get()));
      N->Children.push_back(std::move(After));
      return N;
    }
    case VExpr::FieldAccess: {
      const auto *F = static_cast<const VFieldAccessExpr *>(E);
      auto N = std::make_unique<VCExpr>(VCExpr::Var);
      N->Name = fieldVarName(F);
      N->Sort = F->Base->K == VExpr::Var || F->Base->K == VExpr::Result
                    ? logicSortFor(F->Ty.Kind, intModeOfVType(F->Ty),
                                   F->Ty.BitWidth, F->Ty.IsSigned)
                    : LogicSort();
      N->Loc = F->Loc;
      return N;
    }
    case VExpr::SpecCall: {
      const auto *C = static_cast<const VSpecCallExpr *>(E);
      auto N = std::make_unique<VCExpr>(VCExpr::SpecCall);
      N->SpecCallee = C->CalleeIdentity;
      N->Sort = logicSortFor(C->Ty.Kind, C->Ty.IntMode, C->Ty.BitWidth,
                             C->Ty.IsSigned);
      N->Loc = C->Loc;
      for (const auto &A : C->Args) {
        auto Arg = fromVExpr(A.get());
        if (Arg && (Arg->Sort.Kind == LogicSortKind::BitVector ||
                    Arg->Sort.Kind == LogicSortKind::MathematicalInteger))
          Arg = toMode(std::move(Arg), C->Ty.IntMode);
        N->Children.push_back(std::move(Arg));
      }
      return N;
    }
    case VExpr::OverflowCheck: {
      const auto *O = static_cast<const VOverflowCheckExpr *>(E);
      auto N = std::make_unique<VCExpr>(VCExpr::NoOverflow);
      setBoolSort(*N);
      N->Loc = O->Loc;
      N->OverflowOp = logicOverflowOp(O->Op);
      N->Children.push_back(fromVExpr(O->Lhs.get()));
      if (O->Rhs)
        N->Children.push_back(fromVExpr(O->Rhs.get()));
      return N;
    }
    }
    return fail("unsupported VCR expression kind " +
                std::to_string(static_cast<unsigned>(E->K)));
  }

  static std::string fieldVarName(const VFieldAccessExpr *F) {
    std::string Base;
    if (F->Base->K == VExpr::Var)
      Base = static_cast<const VVarExpr *>(F->Base.get())->Name;
    else if (F->Base->K == VExpr::Result)
      Base = "result";
    else
      Base = "__cppverify_unsupported_field_base";
    return Base + "." + F->Field;
  }

  llvm::Expected<std::unique_ptr<LogicExpr>>
  buildExpression(const VExpr *Expr) {
    auto Result = fromVExpr(Expr);
    std::string ValidationError;
    if (ConstructionError.empty() &&
        !validateLogicExpr(Result.get(), ValidationError))
      ConstructionError = std::move(ValidationError);
    if (!ConstructionError.empty())
      return llvm::createStringError(llvm::inconvertibleErrorCode(), "%s",
                                     ConstructionError.c_str());
    return std::move(Result);
  }

  llvm::Expected<ObligationModule> buildPassive(const PassiveProgram &P) {
    ObligationModule M;
    M.FunctionName = P.FunctionName;
    M.FunctionIdentity = P.FunctionIdentity;
    M.ResultVarName = P.ResultVarName;
    M.HeapPrefix =
        P.OldHeapName.empty() ? std::string(VHeapName) + "_0" : P.OldHeapName;
    CurHeap = M.HeapPrefix;
    for (const auto &[InternalName, Variable] : P.ModelVariables) {
      LogicSort Sort =
          logicSortFor(Variable.Type.Kind, intModeOfVType(Variable.Type),
                       Variable.Type.BitWidth, Variable.Type.IsSigned);
      if (Sort.Kind == LogicSortKind::Invalid) {
        fail("invalid diagnostic variable sort in obligation lowering");
        continue;
      }
      M.DiagnosticVariables[InternalName] = {
          Variable.DisplayName, Sort, Variable.Loc, Variable.EndLoc, {}};
    }
    auto traceKind = [](PassiveTraceKind Kind) {
      switch (Kind) {
      case PassiveTraceKind::Branch:
        return DiagnosticTraceKind::Branch;
      case PassiveTraceKind::Call:
        return DiagnosticTraceKind::Call;
      case PassiveTraceKind::Loop:
        return DiagnosticTraceKind::Loop;
      case PassiveTraceKind::HeapWrite:
        return DiagnosticTraceKind::HeapWrite;
      case PassiveTraceKind::Allocation:
        return DiagnosticTraceKind::Allocation;
      case PassiveTraceKind::LifetimeEnd:
        return DiagnosticTraceKind::LifetimeEnd;
      case PassiveTraceKind::Deallocation:
        return DiagnosticTraceKind::Deallocation;
      case PassiveTraceKind::Return:
        return DiagnosticTraceKind::Return;
      }
      return DiagnosticTraceKind::Branch;
    };
    auto lowerDiagnosticExpr = [&](const VExpr *Expr) {
      const unsigned SemanticQuantifierCounter = QuantifierCounter;
      QuantifierCounter = 0;
      auto Result = fromVExpr(Expr);
      QuantifierCounter = SemanticQuantifierCounter;
      return Result;
    };
    for (const PassiveTraceEvent &Event : P.TraceEvents) {
      DiagnosticTraceEvent Lowered;
      Lowered.Kind = traceKind(Event.Kind);
      Lowered.Message = Event.Message;
      Lowered.Loc = Event.Loc;
      Lowered.EndLoc = Event.EndLoc;
      Lowered.Guard = lowerDiagnosticExpr(Event.Guard.get());
      for (const PassiveTraceValue &Value : Event.Values)
        Lowered.Values.push_back(
            {Value.Label, lowerDiagnosticExpr(Value.Value.get())});
      M.TraceEvents.push_back(std::move(Lowered));
    }

    std::vector<std::unique_ptr<VCExpr>> EntryAssumes;
    for (const auto &Entry : P.EntryAssumes)
      EntryAssumes.push_back(fromVExpr(Entry.get()));

    struct LoweredStmt {
      PassiveStmt::Kind Kind;
      ObligationKind ProofKind;
      uint64_t TraceEventCount;
      std::unique_ptr<VCExpr> Cond;
    };
    std::vector<LoweredStmt> Stmts;
    for (const auto &Stmt : P.Stmts) {
      if (!Stmt) {
        fail("null passive statement in obligation lowering");
        continue;
      }
      Stmts.push_back({Stmt->K, obligationKind(Stmt->ProofKind),
                       Stmt->TraceEventCount, fromVExpr(Stmt->Cond.get())});
    }

    std::vector<std::unique_ptr<VCExpr>> ExitAsserts;
    for (const auto &Exit : P.ExitAsserts)
      ExitAsserts.push_back(fromVExpr(Exit.get()));

    if (!ConstructionError.empty())
      return llvm::createStringError(llvm::inconvertibleErrorCode(), "%s",
                                     ConstructionError.c_str());

    std::vector<const VCExpr *> Assumptions;
    for (const auto &Entry : EntryAssumes)
      Assumptions.push_back(Entry.get());

    auto makeGoal = [&](const VCExpr *Condition) -> std::unique_ptr<VCExpr> {
      std::unique_ptr<VCExpr> ConditionWP = cloneVCExpr(Condition);
      for (auto It = Assumptions.rbegin(); It != Assumptions.rend(); ++It)
        ConditionWP = vcOr(vcNot(cloneVCExpr(*It)), std::move(ConditionWP));
      ConditionWP->Loc = Condition->Loc;
      ConditionWP->EndLoc = Condition->EndLoc;
      return ConditionWP;
    };

    const std::string Identity =
        !P.FunctionIdentity.empty()
            ? P.FunctionIdentity
            : (!P.FunctionName.empty() ? P.FunctionName : "__anonymous");
    unsigned ObligationIndex = 0;
    auto appendObligation = [&](ObligationKind Kind, const VCExpr *Condition,
                                uint64_t TraceEventCount) {
      Obligation Item;
      Item.Kind = Kind;
      Item.Loc = Condition->Loc;
      Item.EndLoc = Condition->EndLoc;
      Item.TraceEventCount = TraceEventCount;
      Item.Id = Identity + "::obligation:" + std::to_string(++ObligationIndex);
      Item.Goal = makeGoal(Condition);
      Item.CounterexampleQuery = vcNot(cloneVCExpr(Item.Goal.get()));
      Item.CounterexampleQuery->Loc = Condition->Loc;
      Item.CounterexampleQuery->EndLoc = Condition->EndLoc;
      M.Obligations.push_back(std::move(Item));
    };

    for (const LoweredStmt &Stmt : Stmts) {
      if (Stmt.Kind == PassiveStmt::Assume) {
        Assumptions.push_back(Stmt.Cond.get());
        continue;
      }
      appendObligation(Stmt.ProofKind, Stmt.Cond.get(), Stmt.TraceEventCount);
    }
    for (const auto &Exit : ExitAsserts)
      appendObligation(ObligationKind::Postcondition, Exit.get(),
                       M.TraceEvents.size());

    M.CorrectnessGoal = buildCompleteGoal(M.Obligations);
    M.CounterexampleQuery = vcNot(cloneVCExpr(M.CorrectnessGoal.get()));

    SpecAxiomContext AxiomContext{P.SpecFunctions, P.SpecFuel, P.HiddenSpecs,
                                  P.RevealedSpecs};
    if (llvm::Error Error = materializeLogicFunctions(M, AxiomContext))
      return std::move(Error);

    auto RequiredFeatures = validateObligationModule(M);
    if (!RequiredFeatures)
      return RequiredFeatures.takeError();
    M.RequiredFeatures = *RequiredFeatures;
    return std::move(M);
  }
};

llvm::Expected<LogicFeatureSet>
verify::validateObligationModule(const ObligationModule &M) {
  if (M.FunctionIdentity.empty() || containsEmbeddedNul(M.FunctionIdentity))
    return llvm::createStringError(
        llvm::inconvertibleErrorCode(),
        "obligation module has an invalid function identity");
  if (containsEmbeddedNul(M.FunctionName) ||
      containsEmbeddedNul(M.ResultVarName) || containsEmbeddedNul(M.HeapPrefix))
    return llvm::createStringError(
        llvm::inconvertibleErrorCode(),
        "embedded NUL in obligation module metadata");

  std::string ValidationError;
  std::set<std::string> StableObligationIds;
  std::map<std::string, LogicSort> ModuleVariables;
  for (const auto &[InternalName, Variable] : M.DiagnosticVariables) {
    if (InternalName.empty() || Variable.DisplayName.empty() ||
        containsEmbeddedNul(InternalName) ||
        containsEmbeddedNul(Variable.DisplayName) ||
        containsEmbeddedNul(Variable.Source.File) ||
        !validateLogicSort(Variable.Sort, ValidationError))
      return llvm::createStringError(
          llvm::inconvertibleErrorCode(),
          "obligation module has invalid diagnostic variable metadata");
    if (!validateSource(Variable.Source, ValidationError))
      return llvm::createStringError(llvm::inconvertibleErrorCode(), "%s",
                                     ValidationError.c_str());
    auto [It, Inserted] = ModuleVariables.emplace(InternalName, Variable.Sort);
    if (!Inserted && !equivalentVariableSort(It->second, Variable.Sort))
      return llvm::createStringError(
          llvm::inconvertibleErrorCode(),
          "obligation module has inconsistent diagnostic variable sort");
  }
  for (const DiagnosticTraceEvent &Event : M.TraceEvents) {
    if (containsEmbeddedNul(Event.Message) ||
        containsEmbeddedNul(Event.Source.File))
      return llvm::createStringError(
          llvm::inconvertibleErrorCode(),
          "obligation module has invalid diagnostic trace metadata");
    if (!validateSource(Event.Source, ValidationError))
      return llvm::createStringError(llvm::inconvertibleErrorCode(), "%s",
                                     ValidationError.c_str());
    if (!validateLogicExpr(Event.Guard.get(), ValidationError) ||
        !validateLogicCalls(Event.Guard.get(), M.LogicFunctions,
                            ValidationError) ||
        !validateVariableScopes(Event.Guard.get(), ModuleVariables,
                                ValidationError) ||
        Event.Guard->Sort.Kind != LogicSortKind::Bool)
      return llvm::createStringError(
          llvm::inconvertibleErrorCode(),
          "obligation module has invalid diagnostic trace metadata");
    for (const DiagnosticTraceValue &Value : Event.Values)
      if (Value.Label.empty() || containsEmbeddedNul(Value.Label) ||
          !validateLogicExpr(Value.Value.get(), ValidationError) ||
          !validateLogicCalls(Value.Value.get(), M.LogicFunctions,
                              ValidationError) ||
          !validateVariableScopes(Value.Value.get(), ModuleVariables,
                                  ValidationError))
        return llvm::createStringError(
            llvm::inconvertibleErrorCode(),
            "obligation module has invalid diagnostic trace value");
  }
  if (!validateLogicExpr(M.CorrectnessGoal.get(), ValidationError))
    return llvm::createStringError(llvm::inconvertibleErrorCode(), "%s",
                                   ValidationError.c_str());
  if (!validateLogicCalls(M.CorrectnessGoal.get(), M.LogicFunctions,
                          ValidationError))
    return llvm::createStringError(llvm::inconvertibleErrorCode(), "%s",
                                   ValidationError.c_str());
  if (!validateVariableScopes(M.CorrectnessGoal.get(), ModuleVariables,
                              ValidationError))
    return llvm::createStringError(llvm::inconvertibleErrorCode(), "%s",
                                   ValidationError.c_str());
  if (M.CorrectnessGoal->Sort.Kind != LogicSortKind::Bool)
    return llvm::createStringError(llvm::inconvertibleErrorCode(),
                                   "complete correctness goal is not bool");
  if (!validateLogicExpr(M.CounterexampleQuery.get(), ValidationError))
    return llvm::createStringError(llvm::inconvertibleErrorCode(), "%s",
                                   ValidationError.c_str());
  if (!validateLogicCalls(M.CounterexampleQuery.get(), M.LogicFunctions,
                          ValidationError))
    return llvm::createStringError(llvm::inconvertibleErrorCode(), "%s",
                                   ValidationError.c_str());
  if (!validateVariableScopes(M.CounterexampleQuery.get(), ModuleVariables,
                              ValidationError))
    return llvm::createStringError(llvm::inconvertibleErrorCode(), "%s",
                                   ValidationError.c_str());
  if (M.CounterexampleQuery->Sort.Kind != LogicSortKind::Bool)
    return llvm::createStringError(llvm::inconvertibleErrorCode(),
                                   "complete counterexample query is not bool");
  if (!isExactNegation(M.CounterexampleQuery.get(), M.CorrectnessGoal.get()))
    return llvm::createStringError(
        llvm::inconvertibleErrorCode(),
        "complete counterexample query is not the exact negation of its goal");

  LogicFeatureSet RequiredFeatures = 0;
  collectRequiredFeatures(M.CorrectnessGoal.get(), RequiredFeatures);
  collectRequiredFeatures(M.CounterexampleQuery.get(), RequiredFeatures);

  std::set<std::string> ObligationIds;
  for (const Obligation &Item : M.Obligations) {
    if (Item.Id.empty() || containsEmbeddedNul(Item.Id) ||
        containsEmbeddedNul(Item.StableId) ||
        containsEmbeddedNul(Item.Source.File) ||
        !ObligationIds.insert(Item.Id).second)
      return llvm::createStringError(
          llvm::inconvertibleErrorCode(),
          "obligation module has an empty or duplicate obligation identity");
    if ((!Item.StableId.empty() &&
         !StableObligationIds.insert(Item.StableId).second) ||
        containsEmbeddedNul(Item.Source.File))
      return llvm::createStringError(
          llvm::inconvertibleErrorCode(),
          "obligation module has an invalid stable diagnostic identity");
    if (!validateSource(Item.Source, ValidationError))
      return llvm::createStringError(llvm::inconvertibleErrorCode(), "%s",
                                     ValidationError.c_str());
    if (Item.TraceEventCount > M.TraceEvents.size())
      return llvm::createStringError(
          llvm::inconvertibleErrorCode(),
          "obligation module has an invalid diagnostic trace prefix");
    if (!validateLogicExpr(Item.Goal.get(), ValidationError))
      return llvm::createStringError(llvm::inconvertibleErrorCode(), "%s",
                                     ValidationError.c_str());
    if (!validateLogicCalls(Item.Goal.get(), M.LogicFunctions, ValidationError))
      return llvm::createStringError(llvm::inconvertibleErrorCode(), "%s",
                                     ValidationError.c_str());
    if (!validateVariableScopes(Item.Goal.get(), ModuleVariables,
                                ValidationError))
      return llvm::createStringError(llvm::inconvertibleErrorCode(), "%s",
                                     ValidationError.c_str());
    if (Item.Goal->Sort.Kind != LogicSortKind::Bool)
      return llvm::createStringError(llvm::inconvertibleErrorCode(),
                                     "individual correctness goal is not bool");
    if (!validateLogicExpr(Item.CounterexampleQuery.get(), ValidationError))
      return llvm::createStringError(llvm::inconvertibleErrorCode(), "%s",
                                     ValidationError.c_str());
    if (!validateLogicCalls(Item.CounterexampleQuery.get(), M.LogicFunctions,
                            ValidationError))
      return llvm::createStringError(llvm::inconvertibleErrorCode(), "%s",
                                     ValidationError.c_str());
    if (!validateVariableScopes(Item.CounterexampleQuery.get(), ModuleVariables,
                                ValidationError))
      return llvm::createStringError(llvm::inconvertibleErrorCode(), "%s",
                                     ValidationError.c_str());
    if (Item.CounterexampleQuery->Sort.Kind != LogicSortKind::Bool)
      return llvm::createStringError(
          llvm::inconvertibleErrorCode(),
          "individual counterexample query is not bool");
    if (!isExactNegation(Item.CounterexampleQuery.get(), Item.Goal.get()))
      return llvm::createStringError(
          llvm::inconvertibleErrorCode(),
          "individual counterexample query is not the exact negation of its "
          "goal");
    collectRequiredFeatures(Item.Goal.get(), RequiredFeatures);
    collectRequiredFeatures(Item.CounterexampleQuery.get(), RequiredFeatures);
  }

  std::unique_ptr<LogicExpr> CanonicalGoal = buildCompleteGoal(M.Obligations);
  if (!equalLogicExpr(M.CorrectnessGoal.get(), CanonicalGoal.get()))
    return llvm::createStringError(
        llvm::inconvertibleErrorCode(),
        "complete correctness goal does not match the ordered obligations");

  for (const auto &[Identity, Declaration] : M.LogicFunctions) {
    if (Identity.empty() || containsEmbeddedNul(Identity) ||
        Declaration.Identity != Identity ||
        containsEmbeddedNul(Declaration.DisplayName))
      return llvm::createStringError(
          llvm::inconvertibleErrorCode(),
          "logical function declaration identity mismatch");
    if (!validateLogicSort(Declaration.ResultSort, ValidationError) ||
        Declaration.ResultSort.Kind == LogicSortKind::Heap)
      return llvm::createStringError(
          llvm::inconvertibleErrorCode(),
          "logical function has an invalid result sort");
    if (Declaration.DefinitionLevels.size() != Declaration.DefinitionFuel)
      return llvm::createStringError(
          llvm::inconvertibleErrorCode(),
          "logical function definition count does not match its fuel");
    if ((Declaration.DefinitionFuel == 0) !=
        (Declaration.StepDefinition == nullptr))
      return llvm::createStringError(
          llvm::inconvertibleErrorCode(),
          "logical function step definition does not match its fuel");
    std::map<std::string, LogicSort> Parameters;
    for (const LogicFunctionParameter &Parameter : Declaration.Parameters) {
      if (Parameter.Name.empty() || containsEmbeddedNul(Parameter.Name) ||
          !validateLogicSort(Parameter.Sort, ValidationError) ||
          Parameter.Sort.Kind == LogicSortKind::Heap ||
          !Parameters.emplace(Parameter.Name, Parameter.Sort).second)
        return llvm::createStringError(
            llvm::inconvertibleErrorCode(),
            "logical function has an invalid or duplicate parameter");
    }
    if (Declaration.DefinitionFuel > 0) {
      if (!validateLogicExpr(Declaration.StepDefinition.get(), ValidationError))
        return llvm::createStringError(llvm::inconvertibleErrorCode(), "%s",
                                       ValidationError.c_str());
      if (Declaration.StepDefinition->Sort.Kind !=
              Declaration.ResultSort.Kind ||
          Declaration.StepDefinition->Sort.BitWidth !=
              Declaration.ResultSort.BitWidth ||
          Declaration.StepDefinition->Sort.Signedness !=
              Declaration.ResultSort.Signedness)
        return llvm::createStringError(
            llvm::inconvertibleErrorCode(),
            "logical function step result sort mismatch");
      if (!validateLogicCalls(Declaration.StepDefinition.get(),
                              M.LogicFunctions, ValidationError) ||
          !validateVariableScopes(Declaration.StepDefinition.get(),
                                  ValidationError) ||
          !validateDefinitionVariables(Declaration.StepDefinition.get(),
                                       Parameters, {}, ValidationError))
        return llvm::createStringError(llvm::inconvertibleErrorCode(), "%s",
                                       ValidationError.c_str());
      collectRequiredFeatures(Declaration.StepDefinition.get(),
                              RequiredFeatures);
    }
    for (const auto &Definition : Declaration.DefinitionLevels) {
      if (!validateLogicExpr(Definition.get(), ValidationError))
        return llvm::createStringError(llvm::inconvertibleErrorCode(), "%s",
                                       ValidationError.c_str());
      if (Definition->Sort.Kind != Declaration.ResultSort.Kind ||
          Definition->Sort.BitWidth != Declaration.ResultSort.BitWidth ||
          Definition->Sort.Signedness != Declaration.ResultSort.Signedness)
        return llvm::createStringError(
            llvm::inconvertibleErrorCode(),
            "logical function definition result sort mismatch");
      if (!validateLogicCalls(Definition.get(), M.LogicFunctions,
                              ValidationError) ||
          !validateVariableScopes(Definition.get(), ValidationError) ||
          !validateDefinitionVariables(Definition.get(), Parameters, {},
                                       ValidationError))
        return llvm::createStringError(llvm::inconvertibleErrorCode(), "%s",
                                       ValidationError.c_str());
      collectRequiredFeatures(Definition.get(), RequiredFeatures);
    }
  }
  return RequiredFeatures;
}

llvm::Expected<ObligationModule>
verify::buildObligationModule(const PassiveProgram &P) {
  ObligationBuilder B(P.ResultVarName,
                      P.OldHeapName.empty() ? std::string(VHeapName) + "_0"
                                            : P.OldHeapName,
                      P.CallerIntMode, P.HeapVariables);
  return B.buildPassive(P);
}

llvm::Expected<std::unique_ptr<LogicExpr>>
verify::lowerLogicExpr(const VExpr *E, const std::string &ResultVar,
                       const std::string &CurHeap, VIntMode CallerMode) {
  ObligationBuilder B(ResultVar, CurHeap, CallerMode);
  return B.buildExpression(E);
}