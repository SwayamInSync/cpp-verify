//===--- Obligation.cpp ---------------------------------------------------===//
#include "Obligation.h"
#include "../IR/VType.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/Support/Error.h"
#include <algorithm>

using namespace clang;
using namespace verify;

LogicSort LogicSort::boolSort() { return {LogicSortKind::Bool, 0}; }

LogicSort LogicSort::mathematicalInteger() {
  return {LogicSortKind::MathematicalInteger, 0};
}

LogicSort LogicSort::bitVector(unsigned BitWidth, bool IsSigned) {
  (void)IsSigned;
  return {LogicSortKind::BitVector, BitWidth};
}

LogicSort LogicSort::pointer() {
  return {LogicSortKind::Pointer, 0};
}

LogicSort LogicSort::heap() { return {LogicSortKind::Heap, 0}; }

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
    return LogicSort::mathematicalInteger();
  return LogicSort::bitVector(BitWidth, IsSigned);
}

static void setLogicSort(VCExpr &Expr) {
  Expr.Sort = logicSortFor(Expr.TypeKind, Expr.IntMode, Expr.BitWidth,
                           Expr.IsSigned);
}

static void setBoolSort(VCExpr &Expr) {
  Expr.TypeKind = VTypeKind::Bool;
  Expr.Sort = LogicSort::boolSort();
}

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

static bool isIntegerKind(VTypeKind Kind) {
  return Kind == VTypeKind::Int32 || Kind == VTypeKind::Int64;
}

static std::unique_ptr<VCExpr> cloneVCExpr(const VCExpr *E) {
  if (!E)
    return nullptr;
  auto Copy = std::make_unique<VCExpr>(E->K);
  Copy->TypeKind = E->TypeKind;
  Copy->Sort = E->Sort;
  Copy->Loc = E->Loc;
  Copy->IntMode = E->IntMode;
  Copy->IsSigned = E->IsSigned;
  Copy->BitWidth = E->BitWidth;
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

static std::unique_ptr<VCExpr> vcBinary(VCExpr::Kind Kind,
                                        std::unique_ptr<VCExpr> L,
                                        std::unique_ptr<VCExpr> R) {
  auto N = std::make_unique<VCExpr>(Kind);
  setBoolSort(*N);
  N->IntMode = L->IntMode;
  N->IsSigned = L->IsSigned;
  N->BitWidth = L->BitWidth;
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
  N->TypeKind = BitWidth > 32 ? VTypeKind::Int64 : VTypeKind::Int32;
  N->IntMode = VIntMode::Math;
  N->IsSigned = IsSigned;
  N->BitWidth = BitWidth;
  N->IntVal = std::string(Buffer);
  setLogicSort(*N);
  return N;
}

static bool validateLogicExpr(const LogicExpr *Expr, std::string &Error) {
  if (!Expr) {
    Error = "null term in obligation IR";
    return false;
  }
  if (Expr->Sort.Kind == LogicSortKind::Invalid) {
    Error = "untyped term in obligation IR";
    return false;
  }
  for (const auto &Child : Expr->Children)
    if (!validateLogicExpr(Child.get(), Error))
      return false;

  auto requireArity = [&](unsigned Minimum, unsigned Maximum) {
    if (Expr->Children.size() >= Minimum &&
        Expr->Children.size() <= Maximum)
      return true;
    Error = "malformed obligation term: unexpected operand count";
    return false;
  };
  auto sameSort = [](const LogicSort &Left, const LogicSort &Right) {
    return Left.Kind == Right.Kind && Left.BitWidth == Right.BitWidth;
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
    if (Expr->Sort.Kind == LogicSortKind::MathematicalInteger ||
        Expr->Sort.Kind == LogicSortKind::BitVector ||
        Expr->Sort.Kind == LogicSortKind::Pointer)
      return true;
    Error = "integer literal has a non-numeric sort";
    return false;
  case VCExpr::Var:
    return requireArity(0, 0);
  case VCExpr::Not:
    return requireArity(1, 1) &&
           requireSort(LogicSortKind::Bool,
                       "logical negation has a non-boolean result") &&
           requireChildSort(0, LogicSortKind::Bool,
                            "logical negation has a non-boolean operand");
  case VCExpr::Neg:
  case VCExpr::BitNot:
    if (!requireArity(1, 1))
      return false;
    if (!sameSort(Expr->Sort, Expr->Children[0]->Sort)) {
      Error = "unary arithmetic changes its operand sort";
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
           requireSort(LogicSortKind::MathematicalInteger,
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
        !requireSort(LogicSortKind::Bool,
                     "equality has a non-boolean result"))
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
    return true;
  case VCExpr::Add:
  case VCExpr::Sub:
  case VCExpr::Mul:
  case VCExpr::Div:
  case VCExpr::Rem:
  case VCExpr::BitAnd:
  case VCExpr::BitOr:
  case VCExpr::BitXor:
  case VCExpr::Shl:
  case VCExpr::Shr:
    if (!requireArity(2, 2))
      return false;
    if ((Expr->K == VCExpr::Add || Expr->K == VCExpr::Sub ||
         Expr->K == VCExpr::Div) &&
        Expr->Sort.Kind == LogicSortKind::Pointer) {
      const LogicSortKind Left = Expr->Children[0]->Sort.Kind;
      const LogicSortKind Right = Expr->Children[1]->Sort.Kind;
      if ((Left == LogicSortKind::Pointer ||
           Left == LogicSortKind::MathematicalInteger) &&
          (Right == LogicSortKind::Pointer ||
           Right == LogicSortKind::MathematicalInteger))
        return true;
    }
    if (!sameSort(Expr->Sort, Expr->Children[0]->Sort) ||
        !sameSort(Expr->Sort, Expr->Children[1]->Sort)) {
      Error = "arithmetic term " +
              std::to_string(static_cast<unsigned>(Expr->K)) +
              " has result sort " + logicSortName(Expr->Sort.Kind) +
              ", left sort " +
              logicSortName(Expr->Children[0]->Sort.Kind) +
              ", and right sort " +
              logicSortName(Expr->Children[1]->Sort.Kind);
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
                            "heap selection has a non-heap operand");
  case VCExpr::Store:
    return requireArity(4, 4) &&
           requireSort(LogicSortKind::Bool,
                       "heap store relation has a non-boolean result") &&
           requireChildSort(0, LogicSortKind::Heap,
                            "heap store has a non-heap input") &&
           requireChildSort(3, LogicSortKind::Heap,
                            "heap store has a non-heap output");
  case VCExpr::Forall:
  case VCExpr::Exists:
    return requireArity(3, 3) &&
           requireSort(LogicSortKind::Bool,
                       "quantifier has a non-boolean result") &&
           requireChildSort(2, LogicSortKind::Bool,
                            "quantifier has a non-boolean body");
  case VCExpr::NoOverflow:
    if (!requireArity(1, 2) ||
        !requireSort(LogicSortKind::Bool,
                     "overflow predicate has a non-boolean result"))
      return false;
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
    return E->IntMode;
  }

  static VIntMode intModeOfVType(const VType &Ty) {
    if (Ty.Kind == VTypeKind::Int32 || Ty.Kind == VTypeKind::Int64)
      return Ty.IntMode;
    return VIntMode::Machine;
  }

  std::unique_ptr<VCExpr> toMode(std::unique_ptr<VCExpr> E, VIntMode Target) {
    if (!E)
      return E;
    if (E->TypeKind == VTypeKind::Ptr) {
      E->IntMode = Target;
      setLogicSort(*E);
      return E;
    }
    if (intModeOf(E.get()) == Target)
      return E;
    if (Target == VIntMode::Machine) {
      if (E->K == VCExpr::BvToInt && E->Children.size() == 1 &&
          E->Children[0] && E->Children[0]->IntMode == VIntMode::Machine)
        return std::move(E->Children[0]);
      switch (E->K) {
      case VCExpr::IntLit:
        E->IntMode = Target;
        setLogicSort(*E);
        return E;
      case VCExpr::Add:
      case VCExpr::Sub:
      case VCExpr::Mul:
        E->Children[0] = toMode(std::move(E->Children[0]), Target);
        E->Children[1] = toMode(std::move(E->Children[1]), Target);
        E->IntMode = Target;
        setLogicSort(*E);
        return E;
      case VCExpr::Neg:
        E->Children[0] = toMode(std::move(E->Children[0]), Target);
        E->IntMode = Target;
        setLogicSort(*E);
        return E;
      case VCExpr::Ite:
        E->Children[1] = toMode(std::move(E->Children[1]), Target);
        E->Children[2] = toMode(std::move(E->Children[2]), Target);
        E->IntMode = Target;
        setLogicSort(*E);
        return E;
      default:
        break;
      }
    }
    auto N = std::make_unique<VCExpr>(
        Target == VIntMode::Machine ? VCExpr::IntToBv : VCExpr::BvToInt);
    N->IntMode = Target;
    N->TypeKind = E->TypeKind;
    N->IsSigned = E->IsSigned;
    N->BitWidth = E->BitWidth;
    N->Loc = E->Loc;
    setLogicSort(*N);
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
    const unsigned BitWidth = Machine->BitWidth;
    const bool IsSigned = Machine->IsSigned;
    auto InRange = vcAnd(vcBinary(VCExpr::Ge, cloneVCExpr(Math.get()),
                                  mathLimit(BitWidth, IsSigned, true)),
                         vcBinary(VCExpr::Le, cloneVCExpr(Math.get()),
                                  mathLimit(BitWidth, IsSigned, false)));

    auto Converted = toMode(std::move(Math), VIntMode::Machine);
    if (Converted->BitWidth != BitWidth) {
      auto Resize = std::make_unique<VCExpr>(VCExpr::BvResize);
      Resize->TypeKind = Machine->TypeKind;
      Resize->IntMode = VIntMode::Machine;
      Resize->IsSigned = IsSigned;
      Resize->BitWidth = BitWidth;
      Resize->Loc = Converted->Loc;
      setLogicSort(*Resize);
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

    bool HasPointer =
        L->TypeKind == VTypeKind::Ptr || R->TypeKind == VTypeKind::Ptr;
    bool HasBoolean =
        L->TypeKind == VTypeKind::Bool || R->TypeKind == VTypeKind::Bool;
    if ((K == VCExpr::Eq || K == VCExpr::Ne) && !HasPointer && !HasBoolean &&
        isIntegerKind(L->TypeKind) && isIntegerKind(R->TypeKind) &&
        L->IntMode != R->IntMode) {
      if (L->IntMode == VIntMode::Machine)
        return exactCrossModeEquality(K, std::move(L), std::move(R));
      return exactCrossModeEquality(K, std::move(R), std::move(L));
    }
    std::pair<std::unique_ptr<VCExpr>, std::unique_ptr<VCExpr>> Unified;
    if (K == VCExpr::Shl || K == VCExpr::Shr) {
      L = toMode(std::move(L), VIntMode::Machine);
      R = toMode(std::move(R), VIntMode::Machine);
      if (R->BitWidth != L->BitWidth) {
        auto Resize = std::make_unique<VCExpr>(VCExpr::BvResize);
        Resize->TypeKind = R->TypeKind;
        Resize->IntMode = VIntMode::Machine;
        Resize->IsSigned = R->IsSigned;
        Resize->BitWidth = L->BitWidth;
        Resize->Loc = R->Loc;
        setLogicSort(*Resize);
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
    N->IntMode = intModeOf(Unified.first.get());
    N->IsSigned = Unified.first->IsSigned;
    N->BitWidth = Unified.first->BitWidth;
    if (K == VCExpr::Eq || K == VCExpr::Ne || K == VCExpr::Lt ||
        K == VCExpr::Le || K == VCExpr::Gt || K == VCExpr::Ge ||
        K == VCExpr::And || K == VCExpr::Or)
      N->TypeKind = VTypeKind::Bool;
    else
      N->TypeKind = Unified.first->TypeKind;
    N->Loc = Unified.first->Loc;
    setLogicSort(*N);
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
    N->Children.push_back(fromVExpr(Q->Lo.get()));
    N->Children.push_back(fromVExpr(Q->Hi.get()));
    // Quantified machine integers range over the corresponding mathematical
    // interval and are converted back to their bit-vector type at machine
    // operations. This is equivalent within the typed bounds and keeps array
    // indices in Z3's native integer sort instead of mixing quantified
    // bit-vectors with integer-addressed heaps.
    N->IntMode = VIntMode::Math;
    N->BitWidth = Q->BinderType.BitWidth;
    N->IsSigned = Q->BinderType.IsSigned;

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
        HeapVariables(std::move(HeapVariables)),
        CallerIntMode(CallerMode), ForceCallerIntMode(ForceCallerMode) {}

  std::unique_ptr<VCExpr> fromVExpr(const VExpr *E) {
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
      N->TypeKind = L->Ty.Kind;
      N->IsSigned = L->Ty.IsSigned;
      N->BitWidth = L->Ty.BitWidth;
      N->IntMode = ForceCallerIntMode ? CallerIntMode : intModeOfVType(L->Ty);
      N->Loc = L->Loc;
      setLogicSort(*N);
      return N;
    }
    case VExpr::Var: {
      auto N = std::make_unique<VCExpr>(VCExpr::Var);
      const std::string &Name = static_cast<const VVarExpr *>(E)->Name;
      auto Bound = BoundVars.find(Name);
      N->Name = Bound == BoundVars.end() ? Name : Bound->second;
      N->TypeKind = static_cast<const VVarExpr *>(E)->Ty.Kind;
      N->IsSigned = static_cast<const VVarExpr *>(E)->Ty.IsSigned;
      N->BitWidth = static_cast<const VVarExpr *>(E)->Ty.BitWidth;
      N->IntMode = Bound != BoundVars.end() ? BoundVarModes.at(Name)
                   : ForceCallerIntMode
                       ? CallerIntMode
                       : intModeOfVType(static_cast<const VVarExpr *>(E)->Ty);
      N->Loc = E->Loc;
      if (HeapVariables.count(N->Name))
        setHeapSort(*N);
      else
        setLogicSort(*N);
      return N;
    }
    case VExpr::BinOp: {
      const auto *B = static_cast<const VBinOpExpr *>(E);
      auto N =
          fromBin(B->Op, fromVExpr(B->Lhs.get()), fromVExpr(B->Rhs.get()));
      N->Loc = B->Loc;
      return N;
    }
    case VExpr::UnaryOp: {
      const auto *U = static_cast<const VUnaryOpExpr *>(E);
      if (U->Op == VUnaryOp::Neg) {
        auto N = std::make_unique<VCExpr>(VCExpr::Neg);
        N->Children.push_back(fromVExpr(U->Operand.get()));
        N->IntMode = intModeOf(N->Children[0].get());
        N->TypeKind = U->Ty.Kind;
        N->IsSigned = U->Ty.IsSigned;
        N->BitWidth = U->Ty.BitWidth;
        N->Loc = U->Loc;
        setLogicSort(*N);
        return N;
      }
      if (U->Op == VUnaryOp::BitNot) {
        auto N = std::make_unique<VCExpr>(VCExpr::BitNot);
        N->Children.push_back(fromVExpr(U->Operand.get()));
        N->IntMode = intModeOf(N->Children[0].get());
        N->TypeKind = U->Ty.Kind;
        N->IsSigned = U->Ty.IsSigned;
        N->BitWidth = U->Ty.BitWidth;
        N->Loc = U->Loc;
        setLogicSort(*N);
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
      N->TypeKind = C->Ty.Kind;
      N->IntMode = intModeOf(N->Children[1].get());
      N->IsSigned = C->Ty.IsSigned;
      N->BitWidth = C->Ty.BitWidth;
      N->Loc = C->Loc;
      if (N->Children[1]->Sort.Kind == LogicSortKind::Heap &&
          N->Children[2]->Sort.Kind == LogicSortKind::Heap)
        setHeapSort(*N);
      else
        setLogicSort(*N);
      return N;
    }
    case VExpr::Result: {
      auto N = std::make_unique<VCExpr>(VCExpr::Var);
      N->Name = ResultVarName.empty() ? "__result_0" : ResultVarName;
      N->TypeKind = E->Ty.Kind;
      N->IntMode = intModeOfVType(E->Ty);
      N->IsSigned = E->Ty.IsSigned;
      N->BitWidth = E->Ty.BitWidth;
      N->Loc = E->Loc;
      setLogicSort(*N);
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
        Zero->TypeKind = C->FromTy.Kind;
        Zero->IntMode = intModeOfVType(C->FromTy);
        Zero->IsSigned = C->FromTy.IsSigned;
        Zero->BitWidth = C->FromTy.BitWidth;
        Zero->Loc = C->Loc;
        setLogicSort(*Zero);
        auto N = std::make_unique<VCExpr>(VCExpr::Ne);
        setBoolSort(*N);
        N->IntMode =
            C->FromTy.Kind == VTypeKind::Ptr ? VIntMode::Math : Inner->IntMode;
        N->IsSigned = Inner->IsSigned;
        N->BitWidth = Inner->BitWidth;
        N->Loc = C->Loc;
        N->Children.push_back(std::move(Inner));
        N->Children.push_back(std::move(Zero));
        return N;
      }
      if (C->FromTy.Kind == VTypeKind::Bool && C->Ty.Kind != VTypeKind::Bool) {
        auto One = std::make_unique<VCExpr>(VCExpr::IntLit);
        One->IntVal = "1";
        One->TypeKind = C->Ty.Kind;
        One->IntMode = intModeOfVType(C->Ty);
        One->IsSigned = C->Ty.IsSigned;
        One->BitWidth = C->Ty.BitWidth;
        One->Loc = C->Loc;
        setLogicSort(*One);
        auto Zero = std::make_unique<VCExpr>(VCExpr::IntLit);
        Zero->TypeKind = C->Ty.Kind;
        Zero->IntMode = intModeOfVType(C->Ty);
        Zero->IsSigned = C->Ty.IsSigned;
        Zero->BitWidth = C->Ty.BitWidth;
        Zero->Loc = C->Loc;
        setLogicSort(*Zero);
        auto N = std::make_unique<VCExpr>(VCExpr::Ite);
        N->TypeKind = C->Ty.Kind;
        N->IntMode = intModeOfVType(C->Ty);
        N->IsSigned = C->Ty.IsSigned;
        N->BitWidth = C->Ty.BitWidth;
        N->Loc = C->Loc;
        setLogicSort(*N);
        N->Children.push_back(std::move(Inner));
        N->Children.push_back(std::move(One));
        N->Children.push_back(std::move(Zero));
        return N;
      }
      if (C->FromTy.Kind == VTypeKind::Ptr &&
          (C->Ty.Kind == VTypeKind::Int32 || C->Ty.Kind == VTypeKind::Int64)) {
        if (C->Ty.IntMode == VIntMode::Machine) {
          auto N = std::make_unique<VCExpr>(VCExpr::IntToBv);
          N->TypeKind = C->Ty.Kind;
          N->IntMode = VIntMode::Machine;
          N->IsSigned = C->Ty.IsSigned;
          N->BitWidth = C->Ty.BitWidth;
          N->Loc = C->Loc;
          setLogicSort(*N);
          N->Children.push_back(std::move(Inner));
          return N;
        }
        Inner->TypeKind = C->Ty.Kind;
        Inner->IntMode = VIntMode::Math;
        Inner->IsSigned = C->Ty.IsSigned;
        Inner->BitWidth = C->Ty.BitWidth;
        Inner->Loc = C->Loc;
        setLogicSort(*Inner);
        return Inner;
      }
      VIntMode TargetMode = intModeOfVType(C->Ty);
      Inner = toMode(std::move(Inner), TargetMode);
      if (TargetMode == VIntMode::Machine &&
          Inner->BitWidth != C->Ty.BitWidth) {
        auto Resize = std::make_unique<VCExpr>(VCExpr::BvResize);
        Resize->TypeKind = C->Ty.Kind;
        Resize->IntMode = TargetMode;
        Resize->IsSigned = C->Ty.IsSigned;
        Resize->BitWidth = C->Ty.BitWidth;
        Resize->Loc = C->Loc;
        setLogicSort(*Resize);
        Resize->Children.push_back(std::move(Inner));
        Inner = std::move(Resize);
      }
      Inner->TypeKind = C->Ty.Kind;
      Inner->IsSigned = C->Ty.IsSigned;
      Inner->BitWidth = C->Ty.BitWidth;
      Inner->Loc = C->Loc;
      setLogicSort(*Inner);
      return Inner;
    }
    case VExpr::Load: {
      const auto *L = static_cast<const VLoadExpr *>(E);
      std::string Heap = L->HeapVar.empty() ? CurHeap : L->HeapVar;
      auto N = std::make_unique<VCExpr>(VCExpr::Select);
      N->TypeKind = L->Ty.Kind;
      N->IntMode = CallerIntMode;
      N->IsSigned = L->Ty.IsSigned;
      N->BitWidth = L->Ty.BitWidth;
      N->Loc = L->Loc;
      setLogicSort(*N);
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
      N->TypeKind = F->Base->K == VExpr::Var || F->Base->K == VExpr::Result
                        ? F->Ty.Kind
                        : VTypeKind::Unsupported;
      N->IntMode = intModeOfVType(F->Ty);
      N->IsSigned = F->Ty.IsSigned;
      N->BitWidth = F->Ty.BitWidth;
      N->Loc = F->Loc;
      setLogicSort(*N);
      return N;
    }
    case VExpr::SpecCall: {
      const auto *C = static_cast<const VSpecCallExpr *>(E);
      auto N = std::make_unique<VCExpr>(VCExpr::SpecCall);
      N->SpecCallee = C->CalleeIdentity;
      N->TypeKind = C->Ty.Kind;
      N->IntMode = C->Ty.IntMode;
      N->IsSigned = C->Ty.IsSigned;
      N->BitWidth = C->Ty.BitWidth;
      N->Loc = C->Loc;
      setLogicSort(*N);
      for (const auto &A : C->Args) {
        auto Arg = fromVExpr(A.get());
        if (Arg && (Arg->TypeKind == VTypeKind::Int32 ||
                    Arg->TypeKind == VTypeKind::Int64))
          Arg = toMode(std::move(Arg), C->Ty.IntMode);
        N->Children.push_back(std::move(Arg));
      }
      return N;
    }
    case VExpr::OverflowCheck: {
      const auto *O = static_cast<const VOverflowCheckExpr *>(E);
      auto N = std::make_unique<VCExpr>(VCExpr::NoOverflow);
      setBoolSort(*N);
      N->IntMode = VIntMode::Machine;
      N->IsSigned = O->Lhs->Ty.IsSigned;
      N->BitWidth = O->Lhs->Ty.BitWidth;
      N->Loc = O->Loc;
      N->OverflowOp = O->Op;
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
    M.SpecFunctions = P.SpecFunctions;
    M.SpecFuel = P.SpecFuel;
    M.HiddenSpecs = P.HiddenSpecs;
    M.RevealedSpecs = P.RevealedSpecs;
    M.CallerIntMode = P.CallerIntMode;
    CurHeap = M.HeapPrefix;

    std::vector<std::unique_ptr<VCExpr>> EntryAssumes;
    for (const auto &Entry : P.EntryAssumes)
      EntryAssumes.push_back(fromVExpr(Entry.get()));

    struct LoweredStmt {
      PassiveStmt::Kind Kind;
      std::unique_ptr<VCExpr> Cond;
    };
    std::vector<LoweredStmt> Stmts;
    for (const auto &Stmt : P.Stmts) {
      if (!Stmt) {
        fail("null passive statement in obligation lowering");
        continue;
      }
      Stmts.push_back({Stmt->K, fromVExpr(Stmt->Cond.get())});
    }

    std::vector<std::unique_ptr<VCExpr>> ExitAsserts;
    for (const auto &Exit : P.ExitAsserts)
      ExitAsserts.push_back(fromVExpr(Exit.get()));

    if (!ConstructionError.empty())
      return llvm::createStringError(llvm::inconvertibleErrorCode(), "%s",
                                     ConstructionError.c_str());

    std::unique_ptr<VCExpr> WP = vcTrue();
    for (const auto &Exit : ExitAsserts)
      WP = vcAnd(std::move(WP), cloneVCExpr(Exit.get()));

    for (auto It = Stmts.rbegin(); It != Stmts.rend(); ++It) {
      auto Cond = cloneVCExpr(It->Cond.get());
      if (It->Kind == PassiveStmt::Assume)
        WP = vcOr(vcNot(std::move(Cond)), std::move(WP));
      else
        WP = vcAnd(std::move(Cond), std::move(WP));
    }

    for (auto It = EntryAssumes.rbegin(); It != EntryAssumes.rend(); ++It)
      WP = vcOr(vcNot(cloneVCExpr(It->get())), std::move(WP));

    M.CounterexampleQuery = vcNot(std::move(WP));

    std::vector<const VCExpr *> Assumptions;
    for (const auto &Entry : EntryAssumes)
      Assumptions.push_back(Entry.get());

    auto makeCounterexampleQuery =
        [&](const VCExpr *Condition) -> std::unique_ptr<VCExpr> {
      std::unique_ptr<VCExpr> ConditionWP = cloneVCExpr(Condition);
      for (auto It = Assumptions.rbegin(); It != Assumptions.rend(); ++It)
        ConditionWP =
            vcOr(vcNot(cloneVCExpr(*It)), std::move(ConditionWP));
      auto Query = vcNot(std::move(ConditionWP));
      Query->Loc = Condition->Loc;
      return Query;
    };

    const std::string Identity =
        !P.FunctionIdentity.empty()
            ? P.FunctionIdentity
            : (!P.FunctionName.empty() ? P.FunctionName : "__anonymous");
    unsigned ObligationIndex = 0;
    auto appendObligation = [&](ObligationKind Kind, const VCExpr *Condition) {
      Obligation Item;
      Item.Kind = Kind;
      Item.Loc = Condition->Loc;
      Item.Id = Identity + "::obligation:" +
                std::to_string(++ObligationIndex);
      Item.CounterexampleQuery = makeCounterexampleQuery(Condition);
      M.Obligations.push_back(std::move(Item));
    };

    for (const LoweredStmt &Stmt : Stmts) {
      if (Stmt.Kind == PassiveStmt::Assume) {
        Assumptions.push_back(Stmt.Cond.get());
        continue;
      }
      appendObligation(ObligationKind::Assertion, Stmt.Cond.get());
    }
    for (const auto &Exit : ExitAsserts)
      appendObligation(ObligationKind::Postcondition, Exit.get());

    std::string ValidationError;
    if (!validateLogicExpr(M.CounterexampleQuery.get(), ValidationError))
      return llvm::createStringError(llvm::inconvertibleErrorCode(), "%s",
                                     ValidationError.c_str());
    if (M.CounterexampleQuery->Sort.Kind != LogicSortKind::Bool)
      return llvm::createStringError(llvm::inconvertibleErrorCode(),
                                     "complete counterexample query is not bool");
    collectRequiredFeatures(M.CounterexampleQuery.get(), M.RequiredFeatures);
    for (const Obligation &Item : M.Obligations) {
      if (!validateLogicExpr(Item.CounterexampleQuery.get(), ValidationError))
        return llvm::createStringError(llvm::inconvertibleErrorCode(), "%s",
                                       ValidationError.c_str());
      if (Item.CounterexampleQuery->Sort.Kind != LogicSortKind::Bool)
        return llvm::createStringError(
            llvm::inconvertibleErrorCode(),
            "individual counterexample query is not bool");
      collectRequiredFeatures(Item.CounterexampleQuery.get(),
                              M.RequiredFeatures);
    }
    return std::move(M);
  }
};

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