//===--- CVC5Backend.cpp --------------------------------------------------===//
#include "CVC5Backend.h"
#include "ObligationSerialization.h"
#include "ObligationSimplify.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/FileUtilities.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/Program.h"
#include "llvm/Support/ThreadPool.h"
#include "llvm/Support/Threading.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>
#include <chrono>
#include <limits>
#include <map>
#include <optional>
#include <set>
#include <thread>

#if defined(_WIN32)
#include "llvm/Support/Windows/WindowsSupport.h"
#else
#include <cerrno>
#include <csignal>
#include <sys/wait.h>
#endif

using namespace clang;
using namespace verify;

namespace {

constexpr uint64_t MaxSolverOutputBytes = 64 * 1024;

static std::string smtSymbol(llvm::StringRef Prefix, llvm::StringRef Identity) {
  static constexpr char Hex[] = "0123456789abcdef";
  std::string Result = Prefix.str();
  Result.reserve(Result.size() + Identity.size() * 2);
  for (unsigned char Byte : Identity.bytes()) {
    Result.push_back(Hex[Byte >> 4]);
    Result.push_back(Hex[Byte & 0x0f]);
  }
  return Result;
}

static std::string smtInteger(llvm::StringRef Value) {
  if (!Value.consume_front("-"))
    return Value.str();
  return "(- " + Value.str() + ")";
}

static std::string decimalPowerOfTwo(unsigned Exponent) {
  llvm::APInt Value(Exponent + 1, 1);
  Value <<= Exponent;
  llvm::SmallString<128> Buffer;
  Value.toString(Buffer, 10, false);
  return std::string(Buffer);
}

class SMTLibEncoder {
  const ObligationModule &Module;
  std::map<std::string, LogicSort> FreeVariables;
  std::map<std::string, const LogicFunctionDecl *> UsedFunctions;
  std::vector<std::map<std::string, std::string>> BoundScopes;
  std::map<std::string, std::string> Substitutions;
  std::vector<std::string> Axioms;
  uint64_t LocalIndex = 0;
  bool UsesValidPtr = false;
  bool Failed = false;
  std::string Error;

  void fail(llvm::Twine Message) {
    if (Failed)
      return;
    Failed = true;
    Error = Message.str();
  }

  std::string freshLocal(llvm::StringRef Prefix) {
    return (Prefix + llvm::Twine(LocalIndex++)).str();
  }

  std::string sort(const LogicSort &Sort) {
    switch (Sort.Kind) {
    case LogicSortKind::Bool:
      return "Bool";
    case LogicSortKind::MathematicalInteger:
    case LogicSortKind::Pointer:
      return "Int";
    case LogicSortKind::BitVector:
      return "(_ BitVec " + std::to_string(Sort.BitWidth) + ")";
    case LogicSortKind::Heap:
      return "(Array Int Int)";
    case LogicSortKind::Invalid:
      fail("cannot encode an invalid logic sort");
      return "Bool";
    }
    fail("cannot encode an unknown logic sort");
    return "Bool";
  }

  std::string boundVariable(llvm::StringRef Name) const {
    for (auto Scope = BoundScopes.rbegin(); Scope != BoundScopes.rend();
         ++Scope) {
      auto It = Scope->find(Name.str());
      if (It != Scope->end())
        return It->second;
    }
    return {};
  }

  std::string freeVariable(llvm::StringRef Name, const LogicSort &Sort) {
    auto [It, Inserted] = FreeVariables.emplace(Name.str(), Sort);
    const bool Equivalent = It->second.Kind == Sort.Kind &&
                            (Sort.Kind == LogicSortKind::MathematicalInteger ||
                             (It->second.BitWidth == Sort.BitWidth &&
                              It->second.Signedness == Sort.Signedness));
    if (!Inserted && !Equivalent)
      fail("logical variable has inconsistent SMT-LIB sorts: " + Name);
    return smtSymbol("v_", Name);
  }

  std::string functionName(const LogicFunctionDecl &Function) {
    UsedFunctions.emplace(Function.Identity, &Function);
    return smtSymbol("f_", Function.Identity);
  }

  static bool isIntegerSort(const LogicSort &Sort) {
    return Sort.Kind == LogicSortKind::MathematicalInteger ||
           Sort.Kind == LogicSortKind::Pointer;
  }

  std::string intToBV(llvm::StringRef Value, unsigned Width) {
    return "((_ int2bv " + std::to_string(Width) + ") " + Value.str() + ")";
  }

  std::string unsignedBVToInt(llvm::StringRef Value) {
    return "(bv2nat " + Value.str() + ")";
  }

  std::string signedBVToInt(llvm::StringRef Value, unsigned Width) {
    const std::string Local = freshLocal("sbv_");
    return "(let ((" + Local + " " + Value.str() + ")) (ite (= ((_ extract " +
           std::to_string(Width - 1) + " " + std::to_string(Width - 1) + ") " +
           Local + ") #b1) (- (bv2nat " + Local + ") " +
           decimalPowerOfTwo(Width) + ") (bv2nat " + Local + ")))";
  }

  std::string resizeBV(llvm::StringRef Value, const LogicSort &Source,
                       unsigned TargetWidth) {
    if (Source.Kind != LogicSortKind::BitVector || Source.BitWidth == 0 ||
        TargetWidth == 0) {
      fail("cannot resize a non-bitvector SMT-LIB term");
      return "(_ bv0 1)";
    }
    if (Source.BitWidth == TargetWidth)
      return Value.str();
    if (Source.BitWidth < TargetWidth) {
      const char *Op = Source.Signedness == LogicSignedness::Signed
                           ? "sign_extend"
                           : "zero_extend";
      return "((_ " + std::string(Op) + " " +
             std::to_string(TargetWidth - Source.BitWidth) + ") " +
             Value.str() + ")";
    }
    return "((_ extract " + std::to_string(TargetWidth - 1) + " 0) " +
           Value.str() + ")";
  }

  std::string coerce(llvm::StringRef Value, const LogicSort &Source,
                     const LogicSort &Target, bool IsSigned) {
    if (Source.Kind == Target.Kind) {
      if (Source.Kind != LogicSortKind::BitVector ||
          Source.BitWidth == Target.BitWidth)
        return Value.str();
    }
    if (isIntegerSort(Source) && isIntegerSort(Target))
      return Value.str();
    if (isIntegerSort(Source) && Target.Kind == LogicSortKind::BitVector)
      return intToBV(Value, Target.BitWidth);
    if (Source.Kind == LogicSortKind::BitVector && isIntegerSort(Target))
      return IsSigned ? signedBVToInt(Value, Source.BitWidth)
                      : unsignedBVToInt(Value);
    fail("unsupported SMT-LIB sort coercion");
    return "false";
  }

  std::string mathDivision(llvm::StringRef Left, llvm::StringRef Right) {
    const std::string L = freshLocal("div_l_");
    const std::string R = freshLocal("div_r_");
    const std::string Magnitude = "(div (ite (< " + L + " 0) (- " + L + ") " +
                                  L + ") (ite (< " + R + " 0) (- " + R + ") " +
                                  R + "))";
    const std::string Signed = "(ite (xor (< " + L + " 0) (< " + R +
                               " 0)) (- " + Magnitude + ") " + Magnitude + ")";
    return "(let ((" + L + " " + Left.str() + ") (" + R + " " + Right.str() +
           ")) (ite (= " + R + " 0) 0 " + Signed + "))";
  }

  std::string mathRemainder(llvm::StringRef Left, llvm::StringRef Right) {
    const std::string L = freshLocal("rem_l_");
    const std::string R = freshLocal("rem_r_");
    const std::string Q = freshLocal("rem_q_");
    const std::string Quotient = mathDivision(L, R);
    return "(let ((" + L + " " + Left.str() + ") (" + R + " " + Right.str() +
           ")) (let ((" + Q + " " + Quotient + ")) (ite (= " + R + " 0) " + L +
           " (- " + L + " (* " + Q + " " + R + ")))))";
  }

  std::string overflowCheck(const LogicExpr *Expr) {
    if (Expr->Children.empty() ||
        Expr->Children[0]->Sort.Kind != LogicSortKind::BitVector) {
      fail("malformed SMT-LIB overflow predicate");
      return "false";
    }
    const unsigned Width = Expr->Children[0]->Sort.BitWidth;
    std::vector<std::string> Operands;
    for (const auto &Child : Expr->Children) {
      std::string Value = encode(Child.get());
      Operands.push_back(resizeBV(Value, Child->Sort, Width));
    }
    const std::string Left = signedBVToInt(Operands[0], Width);
    const std::string Minimum = "(- " + decimalPowerOfTwo(Width - 1) + ")";
    auto inRange = [&](llvm::StringRef Value) {
      return "(and (<= " + Minimum + " " + Value.str() +
             ") (<= " + Value.str() + " (- " + decimalPowerOfTwo(Width - 1) +
             " 1)))";
    };
    if (Expr->OverflowOp == LogicOverflowOp::Neg)
      return inRange("(- " + Left + ")");
    if (Operands.size() != 2) {
      fail("binary SMT-LIB overflow predicate is missing an operand");
      return "false";
    }
    const std::string Right = signedBVToInt(Operands[1], Width);
    switch (Expr->OverflowOp) {
    case LogicOverflowOp::Add:
      return inRange("(+ " + Left + " " + Right + ")");
    case LogicOverflowOp::Sub:
      return inRange("(- " + Left + " " + Right + ")");
    case LogicOverflowOp::Mul:
      return inRange("(* " + Left + " " + Right + ")");
    case LogicOverflowOp::SignedDiv:
      return "(not (and (= " + Left + " " + Minimum + ") (= " + Right +
             " (- 1))))";
    case LogicOverflowOp::Neg:
      llvm_unreachable("handled above");
    }
    llvm_unreachable("unknown overflow operation");
  }

  std::string encode(const LogicExpr *Expr) {
    if (!Expr) {
      fail("cannot encode a null SMT-LIB term");
      return "false";
    }
    auto Child = [&](unsigned Index) {
      if (Index >= Expr->Children.size()) {
        fail("SMT-LIB term has insufficient operands");
        return std::string("false");
      }
      return encode(Expr->Children[Index].get());
    };
    switch (Expr->K) {
    case LogicExpr::True:
      return "true";
    case LogicExpr::False:
      return "false";
    case LogicExpr::BoolLit:
      return Expr->BoolVal ? "true" : "false";
    case LogicExpr::IntLit:
      if (Expr->Sort.Kind == LogicSortKind::BitVector)
        return intToBV(smtInteger(Expr->IntVal), Expr->Sort.BitWidth);
      return smtInteger(Expr->IntVal);
    case LogicExpr::Var: {
      if (std::string Bound = boundVariable(Expr->Name); !Bound.empty())
        return Bound;
      if (auto It = Substitutions.find(Expr->Name); It != Substitutions.end())
        return It->second;
      return freeVariable(Expr->Name, Expr->Sort);
    }
    case LogicExpr::Not:
      return "(not " + Child(0) + ")";
    case LogicExpr::And:
    case LogicExpr::Or: {
      std::string Result = Expr->K == LogicExpr::And ? "(and" : "(or";
      for (const auto &Operand : Expr->Children)
        Result += " " + encode(Operand.get());
      return Result + ")";
    }
    case LogicExpr::Ite:
      return "(ite " + Child(0) + " " + Child(1) + " " + Child(2) + ")";
    case LogicExpr::Eq:
      return "(= " + Child(0) + " " + Child(1) + ")";
    case LogicExpr::Ne:
      return "(not (= " + Child(0) + " " + Child(1) + "))";
    case LogicExpr::Lt:
    case LogicExpr::Le:
    case LogicExpr::Gt:
    case LogicExpr::Ge: {
      const LogicSort &OperandSort = Expr->Children[0]->Sort;
      const bool Signed = OperandSort.Signedness == LogicSignedness::Signed;
      const char *Op = nullptr;
      if (OperandSort.Kind == LogicSortKind::BitVector) {
        switch (Expr->K) {
        case LogicExpr::Lt:
          Op = Signed ? "bvslt" : "bvult";
          break;
        case LogicExpr::Le:
          Op = Signed ? "bvsle" : "bvule";
          break;
        case LogicExpr::Gt:
          Op = Signed ? "bvsgt" : "bvugt";
          break;
        case LogicExpr::Ge:
          Op = Signed ? "bvsge" : "bvuge";
          break;
        default:
          llvm_unreachable("not a comparison");
        }
      } else {
        switch (Expr->K) {
        case LogicExpr::Lt:
          Op = "<";
          break;
        case LogicExpr::Le:
          Op = "<=";
          break;
        case LogicExpr::Gt:
          Op = ">";
          break;
        case LogicExpr::Ge:
          Op = ">=";
          break;
        default:
          llvm_unreachable("not a comparison");
        }
      }
      return "(" + std::string(Op) + " " + Child(0) + " " + Child(1) + ")";
    }
    case LogicExpr::Add:
    case LogicExpr::Sub:
    case LogicExpr::Mul:
    case LogicExpr::Div:
    case LogicExpr::Rem:
    case LogicExpr::BitAnd:
    case LogicExpr::BitOr:
    case LogicExpr::BitXor:
    case LogicExpr::Shl:
    case LogicExpr::Shr: {
      std::string Left = Child(0);
      std::string Right = Child(1);
      if (Expr->Sort.Kind != LogicSortKind::BitVector) {
        if (Expr->K == LogicExpr::Div)
          return mathDivision(Left, Right);
        if (Expr->K == LogicExpr::Rem)
          return mathRemainder(Left, Right);
      }
      const bool Signed = Expr->Sort.Signedness == LogicSignedness::Signed;
      const char *Op = nullptr;
      switch (Expr->K) {
      case LogicExpr::Add:
        Op = Expr->Sort.Kind == LogicSortKind::BitVector ? "bvadd" : "+";
        break;
      case LogicExpr::Sub:
        Op = Expr->Sort.Kind == LogicSortKind::BitVector ? "bvsub" : "-";
        break;
      case LogicExpr::Mul:
        Op = Expr->Sort.Kind == LogicSortKind::BitVector ? "bvmul" : "*";
        break;
      case LogicExpr::Div:
        Op = Signed ? "bvsdiv" : "bvudiv";
        break;
      case LogicExpr::Rem:
        Op = Signed ? "bvsrem" : "bvurem";
        break;
      case LogicExpr::BitAnd:
        Op = "bvand";
        break;
      case LogicExpr::BitOr:
        Op = "bvor";
        break;
      case LogicExpr::BitXor:
        Op = "bvxor";
        break;
      case LogicExpr::Shl:
        Op = "bvshl";
        break;
      case LogicExpr::Shr:
        Op = Signed ? "bvashr" : "bvlshr";
        break;
      default:
        llvm_unreachable("not a binary arithmetic term");
      }
      return "(" + std::string(Op) + " " + Left + " " + Right + ")";
    }
    case LogicExpr::Neg: {
      std::string Value = Child(0);
      return Expr->Sort.Kind == LogicSortKind::BitVector
                 ? "(bvneg " + Value + ")"
                 : "(- " + Value + ")";
    }
    case LogicExpr::BitNot:
      return "(bvnot " + Child(0) + ")";
    case LogicExpr::ValidPtr:
      UsesValidPtr = true;
      return "(p_valid " + Child(0) + ")";
    case LogicExpr::Select: {
      const std::string Cell = "(select " + Child(0) + " " + Child(1) + ")";
      if (Expr->Sort.Kind == LogicSortKind::Bool)
        return "(not (= " + Cell + " 0))";
      if (Expr->Sort.Kind == LogicSortKind::BitVector)
        return intToBV(Cell, Expr->Sort.BitWidth);
      return Cell;
    }
    case LogicExpr::Store: {
      std::string Value = Child(2);
      const LogicSort &ValueSort = Expr->Children[2]->Sort;
      if (ValueSort.Kind == LogicSortKind::Bool)
        Value = "(ite " + Value + " 1 0)";
      else if (ValueSort.Kind == LogicSortKind::BitVector)
        Value = unsignedBVToInt(Value);
      return "(= " + Child(3) + " (store " + Child(0) + " " + Child(1) + " " +
             Value + "))";
    }
    case LogicExpr::Forall:
    case LogicExpr::Exists: {
      const std::string Lower = Child(0);
      const std::string Upper = Child(1);
      const std::string Binder =
          smtSymbol(("q" + std::to_string(BoundScopes.size()) + "_").c_str(),
                    Expr->Binder);
      BoundScopes.push_back({{Expr->Binder, Binder}});
      const std::string Body = Child(2);
      BoundScopes.pop_back();
      const std::string Range = "(and (<= " + Lower + " " + Binder + ") (< " +
                                Binder + " " + Upper + "))";
      if (Expr->K == LogicExpr::Forall)
        return "(forall ((" + Binder + " Int)) (=> " + Range + " " + Body +
               "))";
      return "(exists ((" + Binder + " Int)) (and " + Range + " " + Body + "))";
    }
    case LogicExpr::IntToBv:
      return intToBV(Child(0), Expr->Sort.BitWidth);
    case LogicExpr::BvToInt: {
      const LogicSort &Source = Expr->Children[0]->Sort;
      return Source.Signedness == LogicSignedness::Signed
                 ? signedBVToInt(Child(0), Source.BitWidth)
                 : unsignedBVToInt(Child(0));
    }
    case LogicExpr::BvResize:
      return resizeBV(Child(0), Expr->Children[0]->Sort, Expr->Sort.BitWidth);
    case LogicExpr::NoOverflow:
      return overflowCheck(Expr);
    case LogicExpr::SpecCall: {
      auto It = Module.LogicFunctions.find(Expr->SpecCallee);
      if (It == Module.LogicFunctions.end()) {
        fail("missing SMT-LIB spec declaration: " + Expr->SpecCallee);
        return "false";
      }
      const LogicFunctionDecl &Function = It->second;
      std::string Application = functionName(Function);
      if (!Expr->Children.empty())
        Application = "(" + Application;
      for (unsigned I = 0; I != Expr->Children.size(); ++I) {
        std::string Argument = Child(I);
        Argument = coerce(
            Argument, Expr->Children[I]->Sort, Function.Parameters[I].Sort,
            Function.Parameters[I].Sort.Signedness == LogicSignedness::Signed);
        Application += " " + Argument;
      }
      if (!Expr->Children.empty())
        Application += ")";
      return coerce(Application, Function.ResultSort, Expr->Sort,
                    Function.ResultSort.Signedness == LogicSignedness::Signed);
    }
    }
    fail("unsupported SMT-LIB expression");
    return "false";
  }

  static void collectSpecCalls(const LogicExpr *Expr,
                               std::vector<const LogicExpr *> &Calls) {
    if (!Expr)
      return;
    if (Expr->K == LogicExpr::SpecCall)
      Calls.push_back(Expr);
    for (const auto &Child : Expr->Children)
      collectSpecCalls(Child.get(), Calls);
  }

  void emitSpecAxiom(const LogicExpr *Call) {
    auto It = Module.LogicFunctions.find(Call->SpecCallee);
    if (It == Module.LogicFunctions.end()) {
      fail("missing SMT-LIB spec definition: " + Call->SpecCallee);
      return;
    }
    const LogicFunctionDecl &Function = It->second;
    if (Function.DefinitionLevels.empty())
      return;
    std::vector<std::string> Arguments;
    for (unsigned I = 0; I != Call->Children.size(); ++I) {
      std::string Argument = encode(Call->Children[I].get());
      Arguments.push_back(coerce(
          Argument, Call->Children[I]->Sort, Function.Parameters[I].Sort,
          Function.Parameters[I].Sort.Signedness == LogicSignedness::Signed));
    }
    std::string Left = functionName(Function);
    if (!Arguments.empty())
      Left = "(" + Left;
    for (const std::string &Argument : Arguments)
      Left += " " + Argument;
    if (!Arguments.empty())
      Left += ")";

    std::vector<std::pair<std::string, std::optional<std::string>>> Saved;
    for (unsigned I = 0; I != Function.Parameters.size(); ++I) {
      const std::string &Name = Function.Parameters[I].Name;
      auto Existing = Substitutions.find(Name);
      Saved.emplace_back(Name,
                         Existing == Substitutions.end()
                             ? std::optional<std::string>()
                             : std::optional<std::string>(Existing->second));
      Substitutions[Name] = Arguments[I];
    }
    for (const auto &Definition : Function.DefinitionLevels) {
      std::string Right = encode(Definition.get());
      Right = coerce(Right, Definition->Sort, Function.ResultSort,
                     Function.ResultSort.Signedness == LogicSignedness::Signed);
      Axioms.push_back("(assert (= " + Left + " " + Right + "))");
    }
    for (const auto &[Name, Value] : Saved) {
      if (Value)
        Substitutions[Name] = *Value;
      else
        Substitutions.erase(Name);
    }
  }

public:
  explicit SMTLibEncoder(const ObligationModule &Module) : Module(Module) {}

  llvm::Expected<std::string> run(const LogicExpr *Query) {
    if (!Query)
      return llvm::createStringError(llvm::inconvertibleErrorCode(),
                                     "missing SMT-LIB counterexample query");
    std::vector<const LogicExpr *> Calls;
    collectSpecCalls(Query, Calls);
    for (const LogicExpr *Call : Calls)
      emitSpecAxiom(Call);
    const std::string EncodedQuery = encode(Query);
    if (Failed)
      return llvm::createStringError(llvm::inconvertibleErrorCode(), "%s",
                                     Error.c_str());

    std::string Script;
    llvm::raw_string_ostream Out(Script);
    Out << "(set-logic ALL)\n";
    Out << "(set-option :print-success false)\n";
    for (const auto &[Name, VariableSort] : FreeVariables)
      Out << "(declare-fun " << smtSymbol("v_", Name) << " () "
          << sort(VariableSort) << ")\n";
    if (UsesValidPtr)
      Out << "(declare-fun p_valid (Int) Bool)\n";
    for (const auto &[Identity, Function] : UsedFunctions) {
      (void)Identity;
      Out << "(declare-fun " << smtSymbol("f_", Function->Identity) << " (";
      for (unsigned I = 0; I != Function->Parameters.size(); ++I) {
        if (I != 0)
          Out << " ";
        Out << sort(Function->Parameters[I].Sort);
      }
      Out << ") " << sort(Function->ResultSort) << ")\n";
    }
    for (const std::string &Axiom : Axioms)
      Out << Axiom << "\n";
    Out << "(assert " << EncodedQuery << ")\n";
    Out << "(check-sat)\n";
    Out << "(exit)\n";
    Out.flush();
    if (Failed)
      return llvm::createStringError(llvm::inconvertibleErrorCode(), "%s",
                                     Error.c_str());
    return Script;
  }
};

static VerifyResult querySizeLimitResult(const ObligationModule &Module,
                                         uint64_t MaxQueryNodes,
                                         llvm::StringRef BackendName) {
  VerifyResult Result;
  if (MaxQueryNodes == 0 || obligationModuleNodeCount(Module) <= MaxQueryNodes)
    return Result;
  Result.Status = VerifyStatus::Unresolved;
  Result.Reason = VerifyReason::QuerySizeLimit;
  Result.Message = "canonical obligation module exceeds query node budget " +
                   std::to_string(MaxQueryNodes);
  Result.BackendName = BackendName.str();
  return Result;
}

static std::optional<std::string> readSolverOutput(llvm::StringRef Path,
                                                   std::string &Error) {
  uint64_t Size = 0;
  if (std::error_code EC = llvm::sys::fs::file_size(Path, Size)) {
    Error = "cannot inspect solver output: " + EC.message();
    return std::nullopt;
  }
  if (Size > MaxSolverOutputBytes) {
    Error = "solver output exceeds the 64 KiB limit";
    return std::nullopt;
  }
  auto Buffer = llvm::MemoryBuffer::getFile(Path, false, false);
  if (!Buffer) {
    Error = "cannot read solver output: " + Buffer.getError().message();
    return std::nullopt;
  }
  return (*Buffer)->getBuffer().str();
}

static std::string diagnosticText(llvm::StringRef Text) {
  Text = Text.trim();
  if (Text.size() > 1024)
    Text = Text.take_front(1024);
  return Text.str();
}

enum class ProcessPollState { Running, Exited, Failed };

struct ProcessPollResult {
  ProcessPollState State = ProcessPollState::Running;
  int ExitCode = -1;
  std::string Error;
};

static ProcessPollResult pollProcess(const llvm::sys::ProcessInfo &Process) {
#if defined(_WIN32)
  std::string Error;
  llvm::sys::ProcessInfo Waited =
      llvm::sys::Wait(Process, 0, &Error, nullptr, true);
  if (Waited.Pid == llvm::sys::ProcessInfo::InvalidPid)
    return {ProcessPollState::Running, -1, {}};
  if (Waited.Pid != Process.Pid)
    return {ProcessPollState::Failed, -1,
            Error.empty() ? "cannot poll cvc5 process" : std::move(Error)};
  return {ProcessPollState::Exited, Waited.ReturnCode, std::move(Error)};
#else
  int Status = 0;
  pid_t Waited;
  do {
    Waited = ::waitpid(Process.Pid, &Status, WNOHANG);
  } while (Waited == -1 && errno == EINTR);
  if (Waited == 0)
    return {};
  if (Waited == -1)
    return {ProcessPollState::Failed, -1,
            "cannot poll cvc5 process: " +
                std::error_code(errno, std::generic_category()).message()};
  if (WIFEXITED(Status))
    return {ProcessPollState::Exited, WEXITSTATUS(Status), {}};
  if (WIFSIGNALED(Status))
    return {ProcessPollState::Exited, -2,
            "cvc5 terminated by signal " + std::to_string(WTERMSIG(Status))};
  return {ProcessPollState::Failed, -1,
          "cvc5 changed to an unsupported process state"};
#endif
}

static bool terminateAndReap(const llvm::sys::ProcessInfo &Process,
                             std::string &Error) {
#if defined(_WIN32)
  if (!::TerminateProcess(static_cast<HANDLE>(Process.Process), 1) &&
      ::GetLastError() != ERROR_ACCESS_DENIED) {
    Error = "cannot terminate cvc5 process";
    return false;
  }
  std::string WaitError;
  llvm::sys::ProcessInfo Waited =
      llvm::sys::Wait(Process, std::nullopt, &WaitError);
  if (Waited.Pid != Process.Pid) {
    Error =
        WaitError.empty() ? "cannot reap cvc5 process" : std::move(WaitError);
    return false;
  }
  return true;
#else
  if (::kill(Process.Pid, SIGKILL) == -1 && errno != ESRCH) {
    Error = "cannot terminate cvc5 process: " +
            std::error_code(errno, std::generic_category()).message();
    return false;
  }
  int Status = 0;
  pid_t Waited;
  do {
    Waited = ::waitpid(Process.Pid, &Status, 0);
  } while (Waited == -1 && errno == EINTR);
  if (Waited == -1 && errno != ECHILD) {
    Error = "cannot reap cvc5 process: " +
            std::error_code(errno, std::generic_category()).message();
    return false;
  }
  return true;
#endif
}

static bool solverOutputWithinLimit(llvm::StringRef OutputPath,
                                    llvm::StringRef ErrorPath,
                                    std::string &Error) {
  uint64_t OutputSize = 0;
  uint64_t ErrorSize = 0;
  if (std::error_code EC = llvm::sys::fs::file_size(OutputPath, OutputSize)) {
    Error = "cannot inspect cvc5 output: " + EC.message();
    return false;
  }
  if (std::error_code EC = llvm::sys::fs::file_size(ErrorPath, ErrorSize)) {
    Error = "cannot inspect cvc5 error output: " + EC.message();
    return false;
  }
  if (OutputSize > MaxSolverOutputBytes ||
      ErrorSize > MaxSolverOutputBytes - OutputSize) {
    Error = "solver output exceeds the 64 KiB limit";
    return false;
  }
  return true;
}

} // namespace

llvm::Expected<std::string>
verify::encodeSMTLibQuery(const ObligationModule &Module,
                          const LogicExpr *Query) {
  auto Features = validateObligationModule(Module);
  if (!Features)
    return Features.takeError();
  if (*Features != Module.RequiredFeatures)
    return llvm::createStringError(
        llvm::inconvertibleErrorCode(),
        "obligation feature declaration does not match validated contents");
  return SMTLibEncoder(Module).run(Query);
}

VerifyResult
verify::lowerSMTLibModule(const ObligationModule &Module,
                          llvm::raw_ostream *SMTLibOut,
                          const BackendExecutionOptions &Execution) {
  VerifyResult Limited =
      querySizeLimitResult(Module, Execution.MaxQueryNodes, "cvc5");
  if (Limited.Reason != VerifyReason::None)
    return Limited;
  auto Script = encodeSMTLibQuery(Module, Module.CounterexampleQuery.get());
  if (!Script) {
    VerifyResult Result;
    Result.Status = VerifyStatus::Unresolved;
    Result.Reason = VerifyReason::EncodingFailure;
    Result.BackendName = "cvc5";
    Result.Message = llvm::toString(Script.takeError());
    return Result;
  }
  if (SMTLibOut)
    *SMTLibOut << *Script;
  VerifyResult Result;
  Result.Status = VerifyStatus::Lowered;
  Result.BackendName = "cvc5";
  return Result;
}

CVC5VerifyBackend::CVC5VerifyBackend(const BackendExecutionOptions &Execution)
    : TimeoutMs(Execution.SolverTimeoutMs),
      ResourceLimit(Execution.SolverResourceLimit), Jobs(Execution.Jobs),
      MaxQueryNodes(Execution.MaxQueryNodes) {
  llvm::StringRef Requested = Execution.CVC5Path.empty()
                                  ? llvm::StringRef("cvc5")
                                  : llvm::StringRef(Execution.CVC5Path);
  auto Program = llvm::sys::findProgramByName(Requested);
  if (Program && llvm::sys::fs::can_execute(*Program))
    SolverPath = *Program;
  else if (!Program)
    SolverPathError = "cannot find cvc5 executable '" + Requested.str() +
                      "': " + Program.getError().message();
  else
    SolverPathError =
        "cvc5 executable is missing or not executable: " + *Program;
}

VerifyResult CVC5VerifyBackend::verifyQuery(const ObligationModule &Module,
                                            const LogicExpr *Query) const {
  VerifyResult Result;
  Result.BackendName = "cvc5";
  if (SolverPath.empty()) {
    Result.Status = VerifyStatus::Unresolved;
    Result.Reason = VerifyReason::SolverUnavailable;
    Result.Message = SolverPathError;
    return Result;
  }
  auto Script = encodeSMTLibQuery(Module, Query);
  if (!Script) {
    Result.Status = VerifyStatus::Unresolved;
    Result.Reason = VerifyReason::EncodingFailure;
    Result.Message = llvm::toString(Script.takeError());
    return Result;
  }

  int InputFD = -1;
  llvm::SmallString<128> InputPath;
  if (std::error_code EC = llvm::sys::fs::createTemporaryFile(
          "cppverify-cvc5", "smt2", InputFD, InputPath)) {
    Result.Status = VerifyStatus::Unresolved;
    Result.Reason = VerifyReason::SolverInvocationFailure;
    Result.Message = "cannot create cvc5 input: " + EC.message();
    return Result;
  }
  llvm::FileRemover RemoveInput(InputPath);
  {
    llvm::raw_fd_ostream Input(InputFD, true);
    Input << *Script;
    Input.flush();
    if (Input.has_error()) {
      Result.Status = VerifyStatus::Unresolved;
      Result.Reason = VerifyReason::SolverInvocationFailure;
      Result.Message = "cannot write cvc5 input: " + Input.error().message();
      return Result;
    }
  }

  llvm::SmallString<128> OutputPath;
  if (std::error_code EC = llvm::sys::fs::createTemporaryFile(
          "cppverify-cvc5", "out", OutputPath)) {
    Result.Status = VerifyStatus::Unresolved;
    Result.Reason = VerifyReason::SolverInvocationFailure;
    Result.Message = "cannot create cvc5 output: " + EC.message();
    return Result;
  }
  llvm::FileRemover RemoveOutput(OutputPath);
  llvm::SmallString<128> ErrorPath;
  if (std::error_code EC = llvm::sys::fs::createTemporaryFile(
          "cppverify-cvc5", "err", ErrorPath)) {
    Result.Status = VerifyStatus::Unresolved;
    Result.Reason = VerifyReason::SolverInvocationFailure;
    Result.Message = "cannot create cvc5 error output: " + EC.message();
    return Result;
  }
  llvm::FileRemover RemoveError(ErrorPath);

  std::vector<std::string> OwnedArgs = {SolverPath, "--lang=smt2", "--seed=0",
                                        "--sat-random-seed=0"};
  if (TimeoutMs != 0)
    OwnedArgs.push_back("--tlimit-per=" + std::to_string(TimeoutMs));
  if (ResourceLimit != 0)
    OwnedArgs.push_back("--rlimit-per=" + std::to_string(ResourceLimit));
  OwnedArgs.push_back(InputPath.str().str());
  llvm::SmallVector<llvm::StringRef, 8> Args;
  for (const std::string &Argument : OwnedArgs)
    Args.push_back(Argument);
  std::optional<llvm::StringRef> Redirects[] = {std::nullopt, OutputPath.str(),
                                                ErrorPath.str()};
  std::string InvocationError;
  bool ExecutionFailed = false;
  llvm::sys::ProcessInfo Process =
      llvm::sys::ExecuteNoWait(SolverPath, Args, std::nullopt, Redirects, 0,
                               &InvocationError, &ExecutionFailed);
  if (ExecutionFailed || Process.Pid == llvm::sys::ProcessInfo::InvalidPid) {
    Result.Status = VerifyStatus::Unresolved;
    Result.Reason = VerifyReason::SolverInvocationFailure;
    Result.Message = InvocationError.empty() ? "cannot start cvc5 process"
                                             : std::move(InvocationError);
    return Result;
  }

  const auto Deadline = std::chrono::steady_clock::now() +
                        std::chrono::milliseconds(TimeoutMs) +
                        std::chrono::seconds(1);
  int ExitCode = -1;
  bool TimedOut = false;
  bool OutputLimitExceeded = false;
  while (true) {
    ProcessPollResult Poll = pollProcess(Process);
    if (Poll.State == ProcessPollState::Exited) {
      ExitCode = Poll.ExitCode;
      InvocationError = std::move(Poll.Error);
      break;
    }
    if (Poll.State == ProcessPollState::Failed) {
      InvocationError = std::move(Poll.Error);
      std::string TerminationError;
      if (!terminateAndReap(Process, TerminationError) &&
          !TerminationError.empty())
        InvocationError += ": " + TerminationError;
      break;
    }

    std::string OutputError;
    if (!solverOutputWithinLimit(OutputPath, ErrorPath, OutputError)) {
      OutputLimitExceeded =
          OutputError == "solver output exceeds the 64 KiB limit";
      InvocationError = std::move(OutputError);
      std::string TerminationError;
      if (!terminateAndReap(Process, TerminationError) &&
          !TerminationError.empty())
        InvocationError += ": " + TerminationError;
      break;
    }
    if (TimeoutMs != 0 && std::chrono::steady_clock::now() >= Deadline) {
      TimedOut = true;
      std::string TerminationError;
      if (!terminateAndReap(Process, TerminationError))
        InvocationError = std::move(TerminationError);
      break;
    }
    std::this_thread::sleep_for(std::chrono::milliseconds(2));
  }

  std::string ReadError;
  std::optional<std::string> StandardError =
      readSolverOutput(ErrorPath, ReadError);
  if (!StandardError) {
    Result.Status = VerifyStatus::Unresolved;
    Result.Reason = VerifyReason::SolverMalformedOutput;
    Result.Message = std::move(ReadError);
    return Result;
  }
  if (OutputLimitExceeded) {
    Result.Status = VerifyStatus::Unresolved;
    Result.Reason = VerifyReason::SolverMalformedOutput;
    Result.Message = std::move(InvocationError);
    return Result;
  }
  if (TimedOut) {
    Result.Status = VerifyStatus::Unresolved;
    Result.Reason = VerifyReason::SolverTimeout;
    Result.Message = InvocationError.empty() ? "cvc5 process timed out"
                                             : std::move(InvocationError);
    return Result;
  }
  if (ExitCode != 0) {
    Result.Status = VerifyStatus::Unresolved;
    Result.Reason = VerifyReason::SolverInvocationFailure;
    Result.Message = "cvc5 exited with status " + std::to_string(ExitCode);
    if (!InvocationError.empty())
      Result.Message += ": " + InvocationError;
    if (!StandardError->empty())
      Result.Message += ": " + diagnosticText(*StandardError);
    return Result;
  }

  std::optional<std::string> StandardOutput =
      readSolverOutput(OutputPath, ReadError);
  if (!StandardOutput) {
    Result.Status = VerifyStatus::Unresolved;
    Result.Reason = VerifyReason::SolverMalformedOutput;
    Result.Message = std::move(ReadError);
    return Result;
  }
  const llvm::StringRef Verdict = llvm::StringRef(*StandardOutput).trim();
  if (!StandardError->empty()) {
    Result.Status = VerifyStatus::Unresolved;
    Result.Reason = VerifyReason::SolverMalformedOutput;
    Result.Message =
        "cvc5 wrote unexpected diagnostics: " + diagnosticText(*StandardError);
    return Result;
  }
  if (Verdict == "unsat") {
    Result.Status = VerifyStatus::Verified;
    return Result;
  }
  if (Verdict == "sat") {
    Result.Status = VerifyStatus::Failed;
    Result.Reason = VerifyReason::Counterexample;
    return Result;
  }
  if (Verdict == "unknown") {
    Result.Status = VerifyStatus::Unresolved;
    Result.Reason = VerifyReason::SolverUnknown;
    Result.Message = "cvc5 returned unknown";
    return Result;
  }
  Result.Status = VerifyStatus::Unresolved;
  Result.Reason = VerifyReason::SolverMalformedOutput;
  Result.Message = Verdict.empty()
                       ? "cvc5 returned no satisfiability result"
                       : "malformed cvc5 output: " + diagnosticText(Verdict);
  return Result;
}

VerifyResult CVC5VerifyBackend::verifyObligation(const ObligationModule &Module,
                                                 const Obligation &Item) const {
  VerifyResult Result = verifyQuery(Module, Item.CounterexampleQuery.get());
  Result.ObligationId = Item.StableId.empty() ? Item.Id : Item.StableId;
  Result.ObligationType = Item.Kind;
  Result.Location = Item.Loc;
  Result.Source = Item.Source;
  if (Result.Status == VerifyStatus::Unresolved)
    Result.Message = "proof obligation " + Result.ObligationId +
                     (Result.Message.empty() ? "" : ": " + Result.Message);
  return Result;
}

std::vector<VerifyResult>
CVC5VerifyBackend::verifyObligations(const ObligationModule &Module) const {
  VerifyResult Limited = querySizeLimitResult(Module, MaxQueryNodes, "cvc5");
  if (Limited.Reason != VerifyReason::None)
    return {std::move(Limited)};
  std::vector<VerifyResult> Results;
  Results.reserve(Module.Obligations.size());
  if (Jobs == 1 || Module.Obligations.size() < 2) {
    for (const Obligation &Item : Module.Obligations)
      Results.push_back(verifyObligation(Module, Item));
    return Results;
  }
  llvm::StdThreadPool Pool(llvm::heavyweight_hardware_concurrency(Jobs));
  std::vector<std::shared_future<VerifyResult>> Futures;
  Futures.reserve(Module.Obligations.size());
  for (size_t I = 0; I != Module.Obligations.size(); ++I)
    Futures.push_back(Pool.async([this, &Module, I] {
      return verifyObligation(Module, Module.Obligations[I]);
    }));
  for (std::shared_future<VerifyResult> &Future : Futures)
    Results.push_back(Future.get());
  return Results;
}

VerifyResult CVC5VerifyBackend::verifyModule(const ObligationModule &Module) {
  VerifyResult Limited = querySizeLimitResult(Module, MaxQueryNodes, "cvc5");
  if (Limited.Reason != VerifyReason::None)
    return Limited;
  if (Module.Obligations.empty())
    return verifyQuery(Module, Module.CounterexampleQuery.get());
  std::vector<VerifyResult> Results = verifyObligations(Module);
  std::optional<VerifyResult> FirstFailure;
  std::optional<VerifyResult> FirstUnresolved;
  for (VerifyResult &Result : Results) {
    if (Result.Status == VerifyStatus::Failed && !FirstFailure)
      FirstFailure = std::move(Result);
    else if (Result.Status == VerifyStatus::Unresolved && !FirstUnresolved)
      FirstUnresolved = std::move(Result);
    else if (Result.Status != VerifyStatus::Verified &&
             Result.Status != VerifyStatus::Failed &&
             Result.Status != VerifyStatus::Unresolved) {
      VerifyResult Invalid;
      Invalid.Status = VerifyStatus::Unresolved;
      Invalid.Reason = VerifyReason::InvalidBackendResult;
      Invalid.Message = "cvc5 obligation returned an invalid status";
      Invalid.BackendName = "cvc5";
      return Invalid;
    }
  }
  if (FirstFailure)
    return std::move(*FirstFailure);
  if (FirstUnresolved)
    return std::move(*FirstUnresolved);
  VerifyResult Result;
  Result.Status = VerifyStatus::Verified;
  Result.BackendName = "cvc5";
  return Result;
}
