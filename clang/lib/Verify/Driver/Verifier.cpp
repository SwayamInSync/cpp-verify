//===--- Verifier.cpp - CppVerify driver ----------------------------------===//
#include "Verifier.h"
#include "../Backend/CVC5Backend.h"
#include "../Backend/Certify.h"
#include "../Backend/ChildProcess.h"
#include "../Backend/Induction.h"
#include "../Backend/LeanBackend.h"
#include "../Backend/LogicTerms.h"
#include "../Backend/Obligation.h"
#include "../Backend/ObligationLowering.h"
#include "../Backend/ObligationSerialization.h"
#include "../Backend/ObligationSimplify.h"
#include "../Backend/ProofCache.h"
#include "../Backend/SpecAxioms.h"
#include "../Backend/TaskGroup.h"
#include "../Backend/Z3Encode.h"
#include "../Frontend/ASTConverter.h"
#include "../IR/VStmt.h"
#include "../Transform/LoopUnroll.h"
#include "../Transform/Origins.h"
#include "../Transform/OutParameters.h"
#include "../Transform/Ownership.h"
#include "../Transform/Passivize.h"
#include "../Transform/SpecInline.h"
#include "../Transform/UBChecks.h"
#include "CppVerifyVersion.h"
#include "DumpIR.h"
#include "LeanAutomation.h"
#include "LeanCertifier.h"
#include "clang/AST/ASTContext.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Frontend/TextDiagnostic.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/FormatVariadic.h"
#include "llvm/Support/GlobPattern.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/MD5.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/Program.h"
#include "llvm/Support/SHA256.h"
#include "llvm/Support/ThreadPool.h"
#include "llvm/Support/Threading.h"
#include "llvm/Support/raw_ostream.h"
#include <atomic>
#include <chrono>
#include <iterator>
#include <mutex>
#include <optional>
#include <thread>
#include <tuple>

using namespace clang;
using namespace verify;

namespace {

/// How deep the driver unfolds inductive predicates in a function, one
/// level more at a time, while its verdict waits on them.
constexpr unsigned MaxUnfoldingDepth = 4;

/// How tightly a C++ operator binds.
int precedence(LogicExpr::Kind K) {
  switch (K) {
  case LogicExpr::Or:
    return 1;
  case LogicExpr::And:
    return 2;
  case LogicExpr::Eq:
  case LogicExpr::Ne:
    return 3;
  case LogicExpr::Lt:
  case LogicExpr::Le:
  case LogicExpr::Gt:
  case LogicExpr::Ge:
    return 4;
  case LogicExpr::Add:
  case LogicExpr::Sub:
    return 5;
  case LogicExpr::Mul:
  case LogicExpr::Div:
  case LogicExpr::Rem:
    return 6;
  case LogicExpr::Not:
  case LogicExpr::Neg:
    return 7;
  default:
    return 9;
  }
}

/// \p Expr spelled as C++ with source names, for messages, parenthesized
/// where an operator around it binds at \p Context (\p Right for its right
/// operand); empty where a term has no spelling here.
std::string sourceText(const LogicExpr *Expr, const ObligationModule &Module,
                       int Context = 0, bool Right = false) {
  if (!Expr)
    return {};
  const int Own = precedence(Expr->K);
  auto wrap = [&](std::string Text) {
    if (Text.empty())
      return Text;
    const bool Associative =
        Expr->K == LogicExpr::Add || Expr->K == LogicExpr::Mul ||
        Expr->K == LogicExpr::And || Expr->K == LogicExpr::Or;
    if (Own < Context || (Own == Context && Right && !Associative))
      return "(" + Text + ")";
    return Text;
  };
  auto binary = [&](const char *Op) -> std::string {
    std::string L = sourceText(Expr->Children[0].get(), Module, Own, false);
    std::string R = sourceText(Expr->Children[1].get(), Module, Own, true);
    if (L.empty() || R.empty())
      return {};
    return wrap(L + " " + Op + " " + R);
  };
  switch (Expr->K) {
  case LogicExpr::True:
    return "true";
  case LogicExpr::False:
    return "false";
  case LogicExpr::IntLit:
    return Expr->IntVal.front() == '-' && Context >= 5
               ? "(" + Expr->IntVal + ")"
               : Expr->IntVal;
  case LogicExpr::BoolLit:
    return Expr->BoolVal ? "true" : "false";
  case LogicExpr::Var:
    if (auto It = Module.DiagnosticVariables.find(Expr->Name);
        It != Module.DiagnosticVariables.end())
      return It->second.DisplayName;
    return Expr->Name;
  case LogicExpr::BvToInt:
  case LogicExpr::IntToBv:
  case LogicExpr::BvResize:
    return sourceText(Expr->Children[0].get(), Module, Context, Right);
  case LogicExpr::Not: {
    const LogicExpr *Inner = Expr->Children[0].get();
    static const std::map<LogicExpr::Kind, LogicExpr::Kind> Opposite = {
        {LogicExpr::Lt, LogicExpr::Ge}, {LogicExpr::Le, LogicExpr::Gt},
        {LogicExpr::Gt, LogicExpr::Le}, {LogicExpr::Ge, LogicExpr::Lt},
        {LogicExpr::Eq, LogicExpr::Ne}, {LogicExpr::Ne, LogicExpr::Eq}};
    if (auto It = Opposite.find(Inner->K); It != Opposite.end()) {
      LogicExpr Flipped(It->second);
      Flipped.Sort = Inner->Sort;
      for (const auto &Child : Inner->Children)
        Flipped.Children.push_back(cloneLogicExpr(Child.get()));
      return sourceText(&Flipped, Module, Context, Right);
    }
    if (Inner->K == LogicExpr::Not)
      return sourceText(Inner->Children[0].get(), Module, Context, Right);
    std::string Text = sourceText(Inner, Module, Own);
    return Text.empty() ? Text : wrap("!" + Text);
  }
  case LogicExpr::Neg: {
    std::string Text = sourceText(Expr->Children[0].get(), Module, Own);
    return Text.empty() ? Text : wrap("-" + Text);
  }
  case LogicExpr::And:
    return binary("&&");
  case LogicExpr::Or:
    return binary("||");
  case LogicExpr::Eq:
    return binary("==");
  case LogicExpr::Ne:
    return binary("!=");
  case LogicExpr::Lt:
    return binary("<");
  case LogicExpr::Le:
    return binary("<=");
  case LogicExpr::Gt:
    return binary(">");
  case LogicExpr::Ge:
    return binary(">=");
  case LogicExpr::Add:
    return binary("+");
  case LogicExpr::Sub:
    return binary("-");
  case LogicExpr::Mul:
    return binary("*");
  case LogicExpr::Div:
    return binary("/");
  case LogicExpr::Rem:
    return binary("%");
  case LogicExpr::SpecCall: {
    std::string Name = Expr->SpecCallee;
    for (const auto *Functions :
         {&Module.LogicFunctions, &Module.EvidenceFunctions})
      if (auto It = Functions->find(Expr->SpecCallee); It != Functions->end())
        Name = It->second.DisplayName;
    std::string Text = Name + "(";
    bool First = true;
    for (const auto &Argument : Expr->Children) {
      if (Argument->Sort.Kind == LogicSortKind::Heap)
        continue;
      std::string Shown = sourceText(Argument.get(), Module);
      if (Shown.empty())
        return {};
      Text += (First ? "" : ", ") + Shown;
      First = false;
    }
    return Text + ")";
  }
  default:
    return {};
  }
}

/// The body that would prove the postcondition of the proof function \p Fn
/// by the induction \p Scheme: a call of \p Fn at each value the scheme's
/// recursion reaches, under the condition that reaches it and the function's
/// precondition there. Empty when some part has no C++ spelling here.
std::string proofOutline(const ObligationModule &Module,
                         const InductionScheme &Scheme, const VFunction &Fn) {
  if (Scheme.Function.empty() || Scheme.Instances.empty())
    return {};
  // One branch per condition of the recursion: its calls, each under the
  // function's precondition at its arguments.
  struct Branch {
    std::string Condition;
    std::vector<std::string> Preconditions;
    std::vector<std::string> Calls;
  };
  std::vector<Branch> Branches;
  for (const InductionInstance &Instance : Scheme.Instances) {
    if (!Instance.Binders.empty() ||
        Instance.Values.size() != Scheme.Variables.size())
      return {};
    std::map<std::string, const LogicExpr *> At;
    for (size_t I = 0; I != Scheme.Variables.size(); ++I)
      At[Scheme.Variables[I].first] = Instance.Values[I].get();
    std::vector<std::string> Arguments;
    for (const auto &[Param, Type] : Fn.Params) {
      (void)Type;
      std::string Argument = Param;
      for (size_t I = 0; I != Scheme.Variables.size(); ++I) {
        auto It = Module.DiagnosticVariables.find(Scheme.Variables[I].first);
        if (It != Module.DiagnosticVariables.end() &&
            It->second.DisplayName == Param)
          Argument = sourceText(Instance.Values[I].get(), Module);
      }
      if (Argument.empty())
        return {};
      Arguments.push_back(std::move(Argument));
    }
    std::string Call = Fn.Name + "(";
    for (size_t I = 0; I != Arguments.size(); ++I)
      Call += (I ? ", " : "") + Arguments[I];
    Call += ");";
    std::string Condition;
    if (Instance.Guard->K != LogicExpr::True) {
      Condition =
          sourceText(Instance.Guard.get(), Module, precedence(LogicExpr::And));
      if (Condition.empty())
        return {};
    }
    auto Same = llvm::find_if(Branches, [&](const Branch &Each) {
      return Each.Condition == Condition;
    });
    if (Same == Branches.end()) {
      Branches.push_back({Condition, {}, {}});
      Same = std::prev(Branches.end());
    }
    for (const auto &Precondition : Module.Preconditions) {
      std::string Shown =
          sourceText(substituteFree(Module, Precondition.get(), At).get(),
                     Module, precedence(LogicExpr::And));
      if (Shown.empty())
        return {};
      if (llvm::find(Same->Preconditions, Shown) == Same->Preconditions.end())
        Same->Preconditions.push_back(std::move(Shown));
    }
    Same->Calls.push_back(std::move(Call));
  }
  std::string Body;
  for (const Branch &Each : Branches) {
    std::string Guard = Each.Condition;
    for (const std::string &Precondition : Each.Preconditions)
      Guard += (Guard.empty() ? "" : " && ") + Precondition;
    std::string Block;
    for (const std::string &Call : Each.Calls)
      Block += " " + Call;
    Body += (Body.empty() ? "" : " ") +
            (Guard.empty() ? "{" + Block + " }"
                           : "if (" + Guard + ") {" + Block + " }");
  }
  if (Fn.Decreases.empty()) {
    std::string Measure;
    for (const auto &Component : Scheme.Measure) {
      std::string Shown = sourceText(Component.get(), Module);
      if (Shown.empty())
        return Body;
      Measure += (Measure.empty() ? "" : ", ") + Shown;
    }
    Body += "', with cppverify::decreases(" + Measure + ")";
    return "'" + Body;
  }
  return "'" + Body + "'";
}

/// The conjuncts of the counterexample query whose goal is \p Goal: the
/// goal is !A1 || ... || !An || C, so they are A1, ..., An and !C, each
/// split at its conjunctions.
void counterexampleConjuncts(const LogicExpr *Goal,
                             std::vector<std::unique_ptr<LogicExpr>> &Out) {
  if (Goal->K == LogicExpr::Or) {
    for (const auto &Child : Goal->Children)
      counterexampleConjuncts(Child.get(), Out);
    return;
  }
  std::vector<const LogicExpr *> Work;
  if (Goal->K == LogicExpr::Not)
    Work.push_back(Goal->Children[0].get());
  else if (Goal->K == LogicExpr::False)
    return;
  else {
    Out.push_back(logicNot(cloneLogicExpr(Goal)));
    return;
  }
  while (!Work.empty()) {
    const LogicExpr *Next = Work.back();
    Work.pop_back();
    if (Next->K == LogicExpr::And) {
      for (const auto &Child : Next->Children)
        Work.push_back(Child.get());
      continue;
    }
    if (Next->K != LogicExpr::True)
      Out.push_back(cloneLogicExpr(Next));
  }
}

bool mentionsVariable(const LogicExpr *Expr, const std::string &Name) {
  if (!Expr)
    return false;
  if (Expr->K == LogicExpr::Var && Expr->Name == Name)
    return true;
  for (const auto &Child : Expr->Children)
    if (mentionsVariable(Child.get(), Name))
      return true;
  return false;
}

/// Binds the pattern variables of \p Pattern so that it equals \p Term. A
/// machine variable seen as an integer, bv_to_int(p), matches an integer
/// term t with p := int_to_bv(t): the instance then speaks of t wherever t
/// fits p's sort, and is a true instance elsewhere too.
bool matchTerm(const LogicExpr *Pattern, const LogicExpr *Term,
               const std::set<std::string> &Variables,
               std::map<std::string, const LogicExpr *> &Bound,
               std::vector<std::unique_ptr<LogicExpr>> &Owned) {
  if (Pattern->K == LogicExpr::BvToInt && Term->K != LogicExpr::BvToInt &&
      Term->Sort.Kind == LogicSortKind::MathematicalInteger &&
      Pattern->Children[0]->K == LogicExpr::Var &&
      Variables.count(Pattern->Children[0]->Name)) {
    const LogicExpr &Machine = *Pattern->Children[0];
    auto Value = std::make_unique<LogicExpr>(LogicExpr::IntToBv);
    Value->Sort = Machine.Sort;
    Value->Children.push_back(cloneLogicExpr(Term));
    auto [It, Inserted] = Bound.emplace(Machine.Name, Value.get());
    if (!Inserted)
      return logicEqual(It->second, Value.get());
    Owned.push_back(std::move(Value));
    return true;
  }
  if (Pattern->K == LogicExpr::Var && Variables.count(Pattern->Name)) {
    if (Pattern->Sort.Kind != Term->Sort.Kind ||
        Pattern->Sort.BitWidth != Term->Sort.BitWidth)
      return false;
    auto [It, Inserted] = Bound.emplace(Pattern->Name, Term);
    return Inserted || logicEqual(It->second, Term);
  }
  if (Pattern->K != Term->K ||
      Pattern->Children.size() != Term->Children.size() ||
      Pattern->IntVal != Term->IntVal || Pattern->Name != Term->Name ||
      Pattern->SpecCallee != Term->SpecCallee ||
      Pattern->CollectionOp != Term->CollectionOp ||
      Pattern->Sort.Kind != Term->Sort.Kind)
    return false;
  for (size_t I = 0; I != Pattern->Children.size(); ++I)
    if (!matchTerm(Pattern->Children[I].get(), Term->Children[I].get(),
                   Variables, Bound, Owned))
      return false;
  return true;
}

/// The value each sort starts from: zero, false, empty, memory of zeros.
class DefaultValues : public CandidateModel {
public:
  std::optional<LogicValue> constant(const std::string &,
                                     const LogicSort &Sort) override {
    switch (Sort.Kind) {
    case LogicSortKind::Bool:
      return LogicValue::boolean(false);
    case LogicSortKind::Heap:
      return LogicValue::heap(HeapValue());
    case LogicSortKind::Seq:
      return LogicValue::sequence({});
    case LogicSortKind::Set:
      return LogicValue::set(HeapValue());
    case LogicSortKind::Multiset:
      return LogicValue::multiset(HeapValue());
    case LogicSortKind::Map:
      return LogicValue::map(HeapValue(), HeapValue());
    default:
      return LogicValue::integer(CertInt());
    }
  }
  std::optional<bool> validPointer(const CertInt &) override { return false; }
  std::optional<LogicValue>
  application(const LogicFunctionDecl &,
              const std::vector<LogicValue> &) override {
    return std::nullopt;
  }
};

void specApplications(const LogicExpr *Expr,
                      std::vector<const LogicExpr *> &Out) {
  if (!Expr)
    return;
  if (Expr->K == LogicExpr::SpecCall)
    Out.push_back(Expr);
  for (const auto &Child : Expr->Children)
    specApplications(Child.get(), Out);
}

/// A counterexample the solver proposed but its check could not evaluate,
/// confirmed by a proof at its input: with the values it gives the source
/// variables fixed, the other variables defined by the query's equations
/// replaced by their definitions (an equation x == t lets any x stand for
/// t), the theorems the query states assumed, and the theorems of the
/// established proof functions \p Lemmas (what each one's verification
/// proved) instantiated where their conclusions' applications match the
/// query's, \p Backend proves that the query holds
/// there. It then fails at that input whatever the values no equation
/// defines, resting on those theorems and contracts.
std::optional<VerifyResult> confirmCounterexample(
    const ObligationModule &Module, const VerifyResult &R,
    const FunctionMap &Functions, const VFunction &Fn,
    const std::map<std::string, std::shared_ptr<const ContractTheorem>> &Lemmas,
    VerifyBackend &Backend) {
  const Obligation *Target = nullptr;
  for (const Obligation &Item : Module.Obligations)
    if (!R.ObligationId.empty() &&
        (Item.Id == R.ObligationId || Item.StableId == R.ObligationId))
      Target = &Item;
  const LogicExpr *Goal =
      Target ? Target->Goal.get() : Module.CorrectnessGoal.get();
  if (!Goal || Module.Obligations.empty())
    return std::nullopt;

  std::vector<std::unique_ptr<LogicExpr>> Literals;
  std::map<std::string, const LogicExpr *> Fixed;
  for (const VerifyModelValue &Value : R.Unchecked) {
    if (!Value.Value)
      continue;
    std::unique_ptr<LogicExpr> Literal;
    const LogicSortKind Kind = Value.Sort.Kind;
    if (Kind == LogicSortKind::Bool &&
        (*Value.Value == "true" || *Value.Value == "false")) {
      Literal = std::make_unique<LogicExpr>(
          *Value.Value == "true" ? LogicExpr::True : LogicExpr::False);
    } else if ((Kind == LogicSortKind::MathematicalInteger ||
                Kind == LogicSortKind::BitVector ||
                Kind == LogicSortKind::Pointer) &&
               !Value.Value->empty() &&
               llvm::all_of(llvm::StringRef(*Value.Value)
                                .drop_front(Value.Value->front() == '-'),
                            [](char C) { return C >= '0' && C <= '9'; })) {
      Literal = std::make_unique<LogicExpr>(LogicExpr::IntLit);
      Literal->IntVal = *Value.Value;
    } else {
      continue;
    }
    Literal->Sort = Value.Sort;
    Fixed[Value.InternalName] = Literal.get();
    Literals.push_back(std::move(Literal));
  }
  std::vector<std::unique_ptr<LogicExpr>> Conjuncts;
  counterexampleConjuncts(Goal, Conjuncts);
  for (auto &Conjunct : Conjuncts)
    Conjunct = substituteFree(Module, Conjunct.get(), Fixed);
  // One-point rule: an equation x == t defines x wherever t does not
  // mention it.
  for (unsigned Budget = 4096; Budget != 0; --Budget) {
    bool Replaced = false;
    for (size_t I = 0; I != Conjuncts.size() && !Replaced; ++I) {
      const LogicExpr *C = Conjuncts[I].get();
      if (C->K != LogicExpr::Eq)
        continue;
      for (unsigned Side : {0U, 1U}) {
        const LogicExpr *Var = C->Children[Side].get();
        const LogicExpr *Value = C->Children[1 - Side].get();
        if (Var->K != LogicExpr::Var || mentionsVariable(Value, Var->Name))
          continue;
        std::unique_ptr<LogicExpr> Definition = cloneLogicExpr(Value);
        const std::string Name = Var->Name;
        Conjuncts.erase(Conjuncts.begin() + I);
        for (auto &Other : Conjuncts)
          Other =
              substituteFree(Module, Other.get(), {{Name, Definition.get()}});
        Replaced = true;
        break;
      }
    }
    if (!Replaced)
      break;
  }

  // The theorems the query states are assumed, not proved, conjunct by
  // conjunct as the query states them.
  std::set<std::string> TheoremKeys;
  for (const auto &Theorem : Module.Theorems) {
    std::vector<std::unique_ptr<LogicExpr>> Parts;
    counterexampleConjuncts(
        logicNot(substituteFree(Module, Theorem.get(), Fixed)).get(), Parts);
    for (const auto &Part : Parts)
      TheoremKeys.insert(logicKey(Part.get()));
  }
  // What only constrains variables no value or equation fixes, without
  // applying a spec, is assumed too, once a checked model shows it can hold:
  // the query then holds at that input for some such values.
  std::set<std::string> Open;
  for (const auto &Conjunct : Conjuncts)
    logicNames(Conjunct.get(), Open);
  std::vector<std::unique_ptr<LogicExpr>> Assumed, Context, Claimed;
  for (auto &Conjunct : Conjuncts) {
    std::vector<const LogicExpr *> Applications;
    specApplications(Conjunct.get(), Applications);
    bool Free = false;
    for (const std::string &Name : Open)
      if (Module.DiagnosticVariables.count(Name) == 0 &&
          mentionsVariable(Conjunct.get(), Name))
        Free = true;
    if (TheoremKeys.count(logicKey(Conjunct.get())))
      Assumed.push_back(std::move(Conjunct));
    else if (Free && Applications.empty())
      Context.push_back(std::move(Conjunct));
    else
      Claimed.push_back(std::move(Conjunct));
  }
  if (Claimed.empty())
    return std::nullopt;

  // The proof functions' postconditions where they speak of these terms.
  std::vector<const LogicExpr *> Terms;
  for (const auto &Conjunct : Claimed)
    specApplications(Conjunct.get(), Terms);
  for (const auto &Conjunct : Assumed)
    specApplications(Conjunct.get(), Terms);
  auto conjunction = [](std::vector<std::unique_ptr<LogicExpr>> Parts) {
    std::unique_ptr<LogicExpr> All;
    for (auto &Part : Parts) {
      if (!All) {
        All = std::move(Part);
        continue;
      }
      auto Both = std::make_unique<LogicExpr>(LogicExpr::And);
      Both->Sort = LogicSort::boolSort();
      Both->Children.push_back(std::move(All));
      Both->Children.push_back(std::move(Part));
      All = std::move(Both);
    }
    if (!All) {
      All = std::make_unique<LogicExpr>(LogicExpr::True);
      All->Sort = LogicSort::boolSort();
    }
    return All;
  };
  // The established proof functions' theorems where their conclusions speak
  // of these terms. An instance gives each variable of a theorem a value:
  // the term the match binds; otherwise every integer, machine integer,
  // pointer, or truth value (a universal); otherwise, for memory or a
  // collection, a value where the premises only it constrains hold, which
  // are then dropped, or else the module's own variable of that name. Any
  // values give an instance of a theorem; these are where the module's
  // facts can meet its premises.
  std::map<std::string, LogicSort> ModuleVariables;
  {
    std::set<std::string> None;
    std::vector<std::pair<std::string, LogicSort>> Free;
    logicFreeVariables(Module.CorrectnessGoal.get(), None, Free);
    ModuleVariables.insert(Free.begin(), Free.end());
  }
  auto variable = [](const std::string &Name, LogicSort Sort) {
    auto Var = std::make_unique<LogicExpr>(LogicExpr::Var);
    Var->Name = Name;
    Var->Sort = Sort;
    return Var;
  };
  // Every value of Sort as a term of an integer binder, if there is one.
  auto overIntegers = [&](const std::string &Binder,
                          const LogicSort &Sort) -> std::unique_ptr<LogicExpr> {
    auto Integer = variable(Binder, LogicSort::mathematicalInteger(64, true));
    auto Zero = [](LogicSort Sort) {
      auto Literal = std::make_unique<LogicExpr>(LogicExpr::IntLit);
      Literal->Sort = Sort;
      return Literal;
    };
    std::unique_ptr<LogicExpr> Value;
    switch (Sort.Kind) {
    case LogicSortKind::MathematicalInteger:
      return Integer;
    case LogicSortKind::BitVector:
      Value = std::make_unique<LogicExpr>(LogicExpr::IntToBv);
      Value->Children.push_back(std::move(Integer));
      break;
    case LogicSortKind::Pointer:
      Value = std::make_unique<LogicExpr>(LogicExpr::Add);
      Value->Children.push_back(Zero(Sort));
      Value->Children.push_back(std::move(Integer));
      break;
    case LogicSortKind::Bool:
      Value = std::make_unique<LogicExpr>(LogicExpr::Ne);
      Value->Children.push_back(std::move(Integer));
      Value->Children.push_back(Zero(LogicSort::mathematicalInteger(64, true)));
      break;
    default:
      return nullptr;
    }
    Value->Sort = Sort;
    return Value;
  };
  std::set<std::string> Contracts;
  constexpr unsigned MaxLemmaInstances = 64;
  unsigned Instances = 0;
  unsigned Lemma = 0;
  for (const auto &[Identity, Theorem] : Lemmas) {
    if (!Theorem || Identity == Fn.Identity)
      continue;
    // Its variables, apart from the module's names.
    const std::string Prefix = "__lemma." + std::to_string(Lemma++) + ".";
    std::set<std::string> None;
    std::vector<std::pair<std::string, LogicSort>> Free;
    for (const auto *Part : {&Theorem->Premises, &Theorem->Conclusions})
      for (const auto &Term : *Part)
        logicFreeVariables(Term.get(), None, Free);
    std::vector<std::unique_ptr<LogicExpr>> Apart;
    std::map<std::string, const LogicExpr *> Renamed;
    std::set<std::string> Variables;
    for (const auto &[Name, Sort] : Free) {
      Apart.push_back(variable(Prefix + Name, Sort));
      Renamed[Name] = Apart.back().get();
      Variables.insert(Prefix + Name);
    }
    std::vector<std::unique_ptr<LogicExpr>> Premises, Conclusions;
    for (const auto &Term : Theorem->Premises)
      Premises.push_back(substituteFree(Module, Term.get(), Renamed));
    for (const auto &Term : Theorem->Conclusions)
      Conclusions.push_back(substituteFree(Module, Term.get(), Renamed));
    std::vector<const LogicExpr *> Patterns;
    for (const auto &Conclusion : Conclusions)
      specApplications(Conclusion.get(), Patterns);
    std::set<std::string> Seen;
    for (const LogicExpr *Pattern : Patterns)
      for (const LogicExpr *Term : Terms) {
        if (Pattern->SpecCallee != Term->SpecCallee ||
            Instances == MaxLemmaInstances)
          continue;
        std::map<std::string, const LogicExpr *> Values;
        std::vector<std::unique_ptr<LogicExpr>> Owned;
        if (!matchTerm(Pattern, Term, Variables, Values, Owned))
          continue;
        std::vector<std::unique_ptr<LogicExpr>> Premise, Conclusion;
        std::vector<std::string> Binders;
        std::set<std::string> Unbound;
        for (const auto &[Name, Sort] : Free) {
          const std::string Own = Prefix + Name;
          if (Values.count(Own))
            continue;
          if (auto Value = overIntegers(Own, Sort)) {
            Binders.push_back(Own);
            Values[Own] = Value.get();
            Owned.push_back(std::move(Value));
          } else {
            Unbound.insert(Own);
          }
        }
        // Premises on unbound memory alone, which nothing else mentions,
        // hold for some value of it (memory of zeros, by the certifier):
        // the theorem then holds without them.
        std::vector<const LogicExpr *> Side;
        std::set<std::string> SideNames;
        for (const auto &Part : Premises) {
          std::set<std::string> Outer;
          std::vector<std::pair<std::string, LogicSort>> Names;
          logicFreeVariables(Part.get(), Outer, Names);
          if (!Names.empty() && llvm::all_of(Names, [&](const auto &Name) {
                return Unbound.count(Name.first) != 0;
              })) {
            Side.push_back(Part.get());
            for (const auto &Name : Names)
              SideNames.insert(Name.first);
          }
        }
        auto mentionsSide = [&](const LogicExpr *E) {
          return llvm::any_of(SideNames, [&](const std::string &Name) {
            return mentionsVariable(E, Name);
          });
        };
        bool Independent = !Side.empty();
        for (const auto *Part : {&Premises, &Conclusions})
          for (const auto &E : *Part)
            if (llvm::find(Side, E.get()) == Side.end() &&
                mentionsSide(E.get()))
              Independent = false;
        if (Independent) {
          DefaultValues Zeros;
          for (const LogicExpr *Fact : Side) {
            std::optional<LogicValue> Holds =
                evaluateTerm(Module, *Fact, Zeros);
            if (!Holds || Holds->K != LogicValue::Kind::Bool || !Holds->Truth)
              Independent = false;
          }
        }
        for (const std::string &Own : Unbound) {
          if (Independent && SideNames.count(Own))
            continue;
          const std::string Name = Own.substr(Prefix.size());
          const LogicSort &Sort = Renamed.at(Name)->Sort;
          auto It = ModuleVariables.find(Name);
          if (It == ModuleVariables.end() || It->second.Kind != Sort.Kind ||
              It->second.BitWidth != Sort.BitWidth ||
              It->second.Signedness != Sort.Signedness)
            continue;
          Owned.push_back(variable(Name, Sort));
          Values[Own] = Owned.back().get();
        }
        for (const auto &Part : Premises)
          if (!Independent || llvm::find(Side, Part.get()) == Side.end())
            Premise.push_back(substituteFree(Module, Part.get(), Values));
        for (const auto &Part : Conclusions)
          Conclusion.push_back(substituteFree(Module, Part.get(), Values));
        auto Instance = std::make_unique<LogicExpr>(LogicExpr::Or);
        Instance->Sort = LogicSort::boolSort();
        Instance->Children.push_back(logicNot(conjunction(std::move(Premise))));
        Instance->Children.push_back(conjunction(std::move(Conclusion)));
        // At zero too: an instance the solver need not search for.
        std::vector<std::unique_ptr<LogicExpr>> Zeros;
        std::map<std::string, const LogicExpr *> AtZero;
        for (const std::string &Binder : Binders) {
          Zeros.push_back(std::make_unique<LogicExpr>(LogicExpr::IntLit));
          Zeros.back()->Sort = LogicSort::mathematicalInteger(64, true);
          AtZero[Binder] = Zeros.back().get();
        }
        std::vector<std::unique_ptr<LogicExpr>> Made;
        if (!Binders.empty())
          Made.push_back(substituteFree(Module, Instance.get(), AtZero));
        for (auto It = Binders.rbegin(); It != Binders.rend(); ++It) {
          if (!mentionsVariable(Instance.get(), *It))
            continue;
          auto Quantifier = std::make_unique<LogicExpr>(LogicExpr::Forall);
          Quantifier->Sort = LogicSort::boolSort();
          Quantifier->Binder = *It;
          Quantifier->Children.push_back(std::move(Instance));
          Instance = std::move(Quantifier);
        }
        Made.push_back(std::move(Instance));
        for (auto &Fact : Made) {
          if (Instances == MaxLemmaInstances ||
              !Seen.insert(logicKey(Fact.get())).second)
            continue;
          Assumed.push_back(std::move(Fact));
          Contracts.insert(Identity);
          ++Instances;
        }
      }
  }

  const Obligation &Like = Target ? *Target : Module.Obligations.front();
  SpecAxiomContext Visibility{Functions, Fn.SpecFuel, Fn.HiddenSpecs,
                              Fn.RevealedSpecs};
  // The module whose one obligation is \p Goal, in Like's place.
  auto moduleFor =
      [&](std::unique_ptr<LogicExpr> Goal) -> std::optional<ObligationModule> {
    ObligationModule Confirm = copyObligationModule(Module);
    Obligation Item;
    Item.Id = Like.Id;
    Item.StableId = Like.StableId;
    Item.Kind = Like.Kind;
    Item.Loc = Like.Loc;
    Item.EndLoc = Like.EndLoc;
    Item.Source = Like.Source;
    Item.Goal = std::move(Goal);
    Item.CounterexampleQuery = logicNot(cloneLogicExpr(Item.Goal.get()));
    Confirm.Obligations.clear();
    Confirm.Obligations.push_back(std::move(Item));
    Confirm.TraceEvents.clear();
    Confirm.Theorems.clear();
    Confirm.Preconditions.clear();
    Confirm.CorrectnessGoal = logicCompleteGoal(Confirm.Obligations);
    Confirm.CounterexampleQuery =
        logicNot(cloneLogicExpr(Confirm.CorrectnessGoal.get()));
    if (llvm::Error Error = materializeLogicFunctions(Confirm, Visibility)) {
      llvm::consumeError(std::move(Error));
      return std::nullopt;
    }
    auto Features = validateObligationModule(Confirm);
    if (!Features) {
      llvm::consumeError(Features.takeError());
      return std::nullopt;
    }
    Confirm.RequiredFeatures = *Features;
    Confirm.Attempt = ModuleAttempt::Confirmation;
    return Confirm;
  };
  // The context can hold: a certified counterexample to its negation.
  if (!Context.empty()) {
    std::vector<std::unique_ptr<LogicExpr>> Copy;
    for (const auto &Part : Context)
      Copy.push_back(cloneLogicExpr(Part.get()));
    std::optional<ObligationModule> Satisfiable =
        moduleFor(logicNot(conjunction(std::move(Copy))));
    if (!Satisfiable ||
        Backend.verify(*Satisfiable).Status != VerifyStatus::Failed)
      return std::nullopt;
  }
  for (auto &Part : Context)
    Assumed.push_back(std::move(Part));
  auto Holds = std::make_unique<LogicExpr>(LogicExpr::Or);
  Holds->Sort = LogicSort::boolSort();
  Holds->Children.push_back(logicNot(conjunction(std::move(Assumed))));
  Holds->Children.push_back(conjunction(std::move(Claimed)));
  std::optional<ObligationModule> Confirm = moduleFor(std::move(Holds));
  if (!Confirm || Backend.verify(*Confirm).Status != VerifyStatus::Verified)
    return std::nullopt;

  VerifyResult Failed = R;
  Failed.Status = VerifyStatus::Failed;
  Failed.Reason = VerifyReason::Counterexample;
  Failed.Model.clear();
  for (const VerifyModelValue &Value : R.Unchecked)
    if (Fixed.count(Value.InternalName))
      Failed.Model.push_back(Value);
  std::string Message;
  for (const VerifyModelValue &Value : Failed.Model) {
    Message += (Message.empty() ? "" : ", ") + Value.DisplayName;
    if (Value.DisplayName != Value.InternalName)
      Message += " [ssa=" + Value.InternalName + "]";
    Message += " [type=" + formatLogicSort(Value.Sort) + "] = " + *Value.Value;
  }
  std::string Using;
  for (const std::string &Identity : Contracts)
    if (auto It = Functions.find(Identity); It != Functions.end())
      Using += (Using.empty() ? "" : ", ") + It->second->Name;
  Failed.Message =
      Message + (Message.empty() ? "" : "; ") +
      "confirmed by a proof at this input" +
      (Using.empty() ? std::string() : " that uses the contract of " + Using) +
      ", since its check could not compute " + R.UncheckedApplication;
  Failed.Trace.clear();
  // It rests on the facts the proof assumed: the theorems of the query and
  // the definitions it applies, and the lemmas' contracts.
  std::vector<const LogicExpr *> Used;
  specApplications(Confirm->CorrectnessGoal.get(), Used);
  for (const LogicExpr *Application : Used)
    Failed.CertifiedWith.insert(Application->SpecCallee);
  Failed.CertifiedWith.insert(Module.AssumedPosts.begin(),
                              Module.AssumedPosts.end());
  Failed.CertifiedWith.insert(Module.AssumedUnfoldings.begin(),
                              Module.AssumedUnfoldings.end());
  Failed.ConfirmedWithContracts = std::move(Contracts);
  Failed.Unchecked.clear();
  Failed.UncheckedApplication.clear();
  Failed.InductionTried.clear();
  return Failed;
}

/// Says in plain words why a verdict that waits on recursive specs stayed
/// unresolved: the counterexample the solver proposed and could not be
/// checked, the inductions tried, and for a proof function a body that
/// would prove it by induction.
void explainUnsettled(VerifyResult &R, const VFunction &Fn,
                      const ObligationModule &Module) {
  if (R.Status != VerifyStatus::Unresolved ||
      (R.Reason != VerifyReason::SpecFuel &&
       R.Reason != VerifyReason::UncheckedCounterexample))
    return;
  std::string Prefix;
  if (llvm::StringRef(R.Message).starts_with("proof obligation "))
    if (size_t At = R.Message.find(": "); At != std::string::npos)
      Prefix = R.Message.substr(0, At + 2);
  std::string Text = R.Message.substr(Prefix.size());
  if (!R.UncheckedApplication.empty()) {
    std::string Values;
    for (const VerifyModelValue &Value : R.Unchecked)
      if (Value.Value)
        Values += (Values.empty() ? "" : ", ") + Value.DisplayName + " = " +
                  *Value.Value;
    const std::string Solver = R.BackendName == "cvc5" ? "cvc5"
                               : R.BackendName == "z3" || R.BackendName == "bmc"
                                   ? "Z3"
                                   : "the solver";
    Text = Solver + " proposed " +
           (Values.empty() ? std::string("a counterexample")
                           : Values + " as a counterexample") +
           ", but checking it needs " + R.UncheckedApplication +
           (R.UncheckedReason.empty() ? std::string()
                                      : " (" + R.UncheckedReason + ")") +
           ", and no proved fact settles it: either the claim is false "
           "there, or it is true and needs a proof by induction";
  }
  if (!R.InductionTried.empty()) {
    std::string Tried;
    for (const std::string &Each : R.InductionTried)
      Tried += (Tried.empty() ? "" : " and induction ") + Each;
    Text += "; induction " + Tried + " did not prove it";
  }
  bool Outlined = false;
  if (Fn.IsProof && R.Reason == VerifyReason::SpecFuel)
    for (const InductionScheme &Scheme : inductionSchemes(Module))
      if (std::string Outline = proofOutline(Module, Scheme, Fn);
          !Outline.empty()) {
        Text += "; a proof by induction " + Scheme.Description +
                " could start from the body " + Outline;
        Outlined = true;
        break;
      }
  if (!Outlined && R.UncheckedApplication.empty() && !R.InductionOnly &&
      R.Reason == VerifyReason::SpecFuel &&
      Text.find("by induction") == std::string::npos)
    Text += "; if the claim holds, it needs a proof by induction: a "
            "recursive proof function that uses it at smaller values";
  R.Message = Prefix + Text;
}

/// The functions a body calls, whose contracts its proof assumes.
static void collectCallees(const std::vector<std::unique_ptr<VStmt>> &Stmts,
                           std::set<std::string> &Out) {
  for (const auto &S : Stmts) {
    switch (S->K) {
    case VStmt::Call:
      Out.insert(static_cast<const VCallStmt &>(*S).CalleeIdentity);
      break;
    case VStmt::If: {
      const auto &I = static_cast<const VIfStmt &>(*S);
      collectCallees(I.Then, Out);
      collectCallees(I.Else, Out);
      break;
    }
    case VStmt::While:
      collectCallees(static_cast<const VWhileStmt &>(*S).Body, Out);
      break;
    case VStmt::Seq:
      collectCallees(static_cast<const VSeqStmt &>(*S).Stmts, Out);
      break;
    case VStmt::GhostBlock:
      collectCallees(static_cast<const VGhostBlockStmt &>(*S).Body, Out);
      break;
    default:
      break;
    }
  }
}

/// The functions the proof blocks of \p Fn's clauses of \p Kinds call.
static std::set<std::string>
clauseProofCallees(const VFunction &Fn,
                   std::initializer_list<VFunction::ClauseProof::Kind> Kinds) {
  std::set<std::string> Out;
  for (const VFunction::ClauseProof &Proof : Fn.ClauseProofs)
    if (llvm::is_contained(Kinds, Proof.K))
      collectCallees(Proof.Body, Out);
  return Out;
}

/// A passive program asking whether its end is reachable: every assertion
/// becomes an assumption, and the end asserts false. With \p EntryOnly only
/// the precondition is kept.
/// Whether Goal holds after the entry assumptions, Extra, and the first
/// Count statements, every assertion among them assumed.
static PassiveProgram smokeProgram(const PassiveProgram &P, size_t Count,
                                   std::unique_ptr<VExpr> Goal,
                                   const VExpr *Extra = nullptr) {
  PassiveProgram Smoke;
  Smoke.FunctionName = P.FunctionName + ".smoke";
  Smoke.FunctionIdentity = P.FunctionIdentity + "::smoke";
  for (const auto &Assume : P.EntryAssumes)
    Smoke.EntryAssumes.push_back(cloneVExpr(Assume.get()));
  if (Extra)
    Smoke.EntryAssumes.push_back(cloneVExpr(Extra));
  for (size_t I = 0; I < Count && I < P.Stmts.size(); ++I) {
    auto Copy = std::make_unique<PassiveStmt>();
    Copy->K = PassiveStmt::Assume;
    Copy->Cond = cloneVExpr(P.Stmts[I]->Cond.get());
    Smoke.Stmts.push_back(std::move(Copy));
  }
  PassiveExitAssert End;
  End.ProofKind = ProofObligationKind::Assertion;
  End.Cond = std::move(Goal);
  Smoke.ExitAsserts.push_back(std::move(End));
  Smoke.ResultVarName = P.ResultVarName;
  Smoke.OldHeapName = P.OldHeapName;
  Smoke.HeapVariables = P.HeapVariables;
  Smoke.SpecFunctions = P.SpecFunctions;
  Smoke.SpecFuel = P.SpecFuel;
  Smoke.HiddenSpecs = P.HiddenSpecs;
  Smoke.RevealedSpecs = P.RevealedSpecs;
  Smoke.CallerIntMode = P.CallerIntMode;
  return Smoke;
}

static bool isDeductiveBackend(BackendKind Kind) {
  return Kind == BackendKind::Z3 || Kind == BackendKind::CVC5 ||
         Kind == BackendKind::Portfolio || Kind == BackendKind::Race;
}

static VerifyResult lowerForBackend(const ObligationModule &Module,
                                    BackendKind Kind,
                                    const BackendExecutionOptions &Execution) {
  if (Kind == BackendKind::CVC5)
    return lowerSMTLibModule(Module, nullptr, Execution);
  if (Kind == BackendKind::Portfolio || Kind == BackendKind::Race) {
    const std::string Name = Kind == BackendKind::Race ? "race" : "portfolio";
    VerifyResult Z3Result = lowerObligationModule(Module, nullptr, Execution);
    if (Z3Result.Status != VerifyStatus::Lowered) {
      Z3Result.BackendName = Name;
      Z3Result.Message =
          "z3 component" +
          (Z3Result.Message.empty() ? std::string() : ": " + Z3Result.Message);
      return Z3Result;
    }
    VerifyResult CVC5Result = lowerSMTLibModule(Module, nullptr, Execution);
    if (CVC5Result.Status != VerifyStatus::Lowered) {
      CVC5Result.BackendName = Name;
      CVC5Result.Message = "cvc5 component" + (CVC5Result.Message.empty()
                                                   ? std::string()
                                                   : ": " + CVC5Result.Message);
      return CVC5Result;
    }
    VerifyResult Result;
    Result.Status = VerifyStatus::Lowered;
    Result.BackendName = Name;
    return Result;
  }
  return lowerObligationModule(Module, nullptr, Execution);
}

struct VerifyDiagnostic {
  enum Kind {
    Lowered,
    Verified,
    Error,
    Unresolved,
    /// A function whose verification Ctrl-C cut short.
    Interrupted,
    BoundedSafe,
    Exported,
    Certified,
    MixedProof,
    Trusted,
    Warning
  };
  Kind K;
  std::string Message;
  SourceLocation Loc;
  std::string FunctionName;
  std::optional<VerifyResult> Result;
  /// For an export to a Lean project: of its goals, how many cppverify_auto
  /// proves.
  unsigned LeanAutomatic = 0;
  /// A certified failure that its refutation shows in Lean too.
  bool LeanRefuted = false;
  /// A proof by a solver, by Lean, or by both, which establishes what it
  /// proves.
  bool isProof() const {
    return K == Verified || K == Certified || K == MixedProof;
  }
  /// No execution reaches the claim, so it holds vacuously.
  bool Vacuous = false;
  /// For a vacuity warning: the verdict it is about, and whether its query
  /// was of the entry state alone, which callee contracts do not enter.
  std::optional<size_t> FindingOf;
  bool FoundAtEntry = false;
  /// For a vacuous verdict: whether the entry state alone is unreachable.
  bool VacuousAtEntry = false;
  /// Proved only for executions that terminate.
  bool Partial = false;
  /// Trusted contracts the proof relies on.
  std::vector<std::string> Trusts;
  /// For a counterexample confirmed by a proof at its input: the proof
  /// functions whose contracts that proof used.
  std::vector<std::string> ConfirmedWith;
  /// Functions not verified that call this one: its precondition is assumed
  /// at those calls.
  std::vector<std::string> UnverifiedCallers;
  /// Kept for the steps that relate verdicts, but not printed: a proof the
  /// verifier generated, which is reported only if it fails.
  bool Quiet = false;
  /// Kept for the steps that relate verdicts, never printed: a verdict of an
  /// interrupted function, which its Interrupted line replaces, or a vacuity
  /// finding that rests on a fact that is not established.
  bool Hidden = false;
  /// For an error about source the verifier cannot represent: that source,
  /// shown with its line as a compiler error is.
  SourceRange Span;
  /// A spec function that needs no check, listed with --verbose: no verdict.
  bool Axiom = false;
  /// What else the verifier found about the verdict, each printed as a note.
  std::vector<std::string> Notes;
  /// A failing obligation after the one a function's verdict reports: no
  /// verdict of its own.
  bool Additional = false;
};

/// The backend a lowering reports, as lower-only names it.
static std::string backendName(BackendKind Kind) {
  return Kind == BackendKind::CVC5        ? "cvc5"
         : Kind == BackendKind::Portfolio ? "portfolio"
         : Kind == BackendKind::Race      ? "race"
                                          : "z3";
}

static std::string lowerFailure(BackendKind Kind) {
  return Kind == BackendKind::Z3 || Kind == BackendKind::BMC
             ? "Z3 lowering failed: "
             : "backend lowering failed: ";
}

static std::string backendSuffix(const VerifyResult &Result) {
  std::string Suffix;
  if (!Result.BackendName.empty()) {
    Suffix = " [backend=" + Result.BackendName;
    if (Result.Bound)
      Suffix += ", bound=" + std::to_string(*Result.Bound);
    Suffix += "]";
  }
  if (Result.CacheHits || Result.CacheMisses || Result.CacheErrors) {
    Suffix += " [cache=" + std::to_string(Result.CacheHits) + "/" +
              std::to_string(Result.CacheHits + Result.CacheMisses +
                             Result.CacheErrors);
    if (Result.CacheErrors)
      Suffix += ", errors=" + std::to_string(Result.CacheErrors);
    Suffix += "]";
  }
  if (!Result.CacheError.empty())
    Suffix += " [cache-error=" + Result.CacheError + "]";
  if (Result.Reason != VerifyReason::None)
    Suffix += " [reason=" + verifyReasonCode(Result.Reason).str() + "]";
  if (Result.ExploredBounds.size() > 1) {
    Suffix += " [bounds=";
    for (size_t I = 0; I != Result.ExploredBounds.size(); ++I) {
      if (I != 0)
        Suffix += ",";
      Suffix += std::to_string(Result.ExploredBounds[I]);
    }
    Suffix += "]";
  }
  if (Result.ReusedQueries)
    Suffix += " [reused-queries=" + std::to_string(Result.ReusedQueries) + "]";
  if (!Result.InductionUsed.empty())
    Suffix += " [by induction " + Result.InductionUsed + "]";
  return Suffix;
}

static llvm::StringRef diagnosticKindCode(VerifyDiagnostic::Kind Kind) {
  switch (Kind) {
  case VerifyDiagnostic::Lowered:
    return "lowered";
  case VerifyDiagnostic::Verified:
    return "verified";
  case VerifyDiagnostic::Error:
    return "error";
  case VerifyDiagnostic::Unresolved:
    return "unresolved";
  case VerifyDiagnostic::Interrupted:
    return "interrupted";
  case VerifyDiagnostic::BoundedSafe:
    return "bounded-safe";
  case VerifyDiagnostic::Exported:
    return "exported";
  case VerifyDiagnostic::Certified:
    return "certified";
  case VerifyDiagnostic::MixedProof:
    return "mixed-proof";
  case VerifyDiagnostic::Trusted:
    return "trusted";
  case VerifyDiagnostic::Warning:
    return "warning";
  }
  return "error";
}

static llvm::StringRef verifyStatusCode(VerifyStatus Status) {
  switch (Status) {
  case VerifyStatus::Lowered:
    return "lowered";
  case VerifyStatus::Verified:
    return "verified";
  case VerifyStatus::Failed:
    return "failed";
  case VerifyStatus::Unresolved:
    return "unresolved";
  case VerifyStatus::BoundedSafe:
    return "bounded-safe";
  case VerifyStatus::Exported:
    return "exported";
  case VerifyStatus::Certified:
    return "certified";
  case VerifyStatus::MixedProof:
    return "mixed-proof";
  }
  return "unresolved";
}

/// "[z3: 18 of 20 proved; lean: 2 exported]" for a Lean fallback.
static std::string evidenceSuffix(const ProofEvidence &Evidence,
                                  llvm::StringRef LeanState) {
  std::string Suffix = " [";
  if (Evidence.SolverProved)
    Suffix += Evidence.Solver + ": " + std::to_string(*Evidence.SolverProved) +
              " of " + std::to_string(Evidence.Total) + " proved; ";
  Suffix += "lean: " + std::to_string(Evidence.LeanObligations.size()) + " " +
            LeanState.str() + "]";
  return Suffix;
}

static llvm::StringRef traceKindCode(DiagnosticTraceKind Kind) {
  switch (Kind) {
  case DiagnosticTraceKind::Branch:
    return "branch";
  case DiagnosticTraceKind::Call:
    return "call";
  case DiagnosticTraceKind::Loop:
    return "loop";
  case DiagnosticTraceKind::HeapWrite:
    return "heap-write";
  case DiagnosticTraceKind::Allocation:
    return "allocation";
  case DiagnosticTraceKind::LifetimeEnd:
    return "lifetime-end";
  case DiagnosticTraceKind::Deallocation:
    return "deallocation";
  case DiagnosticTraceKind::Return:
    return "return";
  }
  return "branch";
}

static std::string jsonText(llvm::StringRef Text) {
  return llvm::json::isUTF8(Text) ? Text.str() : llvm::json::fixUTF8(Text);
}

static llvm::json::Object sourceJSON(const ObligationSource &Source) {
  llvm::json::Object Result;
  if (!Source.isValid())
    return Result;
  Result["file"] = jsonText(Source.File);
  Result["line"] = Source.Line;
  Result["column"] = Source.Column;
  Result["end_line"] = Source.EndLine != 0 ? Source.EndLine : Source.Line;
  Result["end_column"] =
      Source.EndColumn != 0 ? Source.EndColumn : Source.Column;
  return Result;
}

static std::string leanProjectPath(llvm::StringRef Root,
                                   llvm::ArrayRef<llvm::StringRef> Components) {
  llvm::SmallString<256> Path(Root);
  for (llvm::StringRef Component : Components)
    llvm::sys::path::append(Path, Component);
  return std::string(Path);
}

static llvm::Error writeTextFile(llvm::StringRef Path,
                                 llvm::StringRef Contents) {
  std::error_code EC;
  llvm::raw_fd_ostream OS(Path, EC, llvm::sys::fs::OF_Text);
  if (EC)
    return llvm::createStringError(EC, "cannot write %s", Path.str().c_str());
  OS << Contents;
  OS.flush();
  if (OS.has_error())
    return llvm::createStringError(OS.error(), "cannot write %s",
                                   Path.str().c_str());
  return llvm::Error::success();
}

// A generated file is rewritten only when it changes, so that a rerun of the
// same source leaves every file as it was.
static llvm::Error writeTextFileIfChanged(llvm::StringRef Path,
                                          llvm::StringRef Contents) {
  if (auto Buffer = llvm::MemoryBuffer::getFile(Path, /*IsText=*/true))
    if ((*Buffer)->getBuffer() == Contents)
      return llvm::Error::success();
  return writeTextFile(Path, Contents);
}

static constexpr llvm::StringLiteral LeanGeneratedNote =
    "/- Generated by CppVerify. Regeneration replaces this file, never a "
    "proof. -/";

// What each module of goals starts with: options and the instance attribute
// of the prelude's classical decidability are local to a file.
static constexpr llvm::StringLiteral LeanGoalModulePreamble =
    "noncomputable section\n\n"
    "set_option maxRecDepth 100000\n"
    "set_option maxHeartbeats 0\n\n"
    "attribute [local instance] cppVerifyPropDecidable\n\n";

static llvm::Error writeTextFileIfMissing(llvm::StringRef Path,
                                          llvm::StringRef Contents) {
  if (llvm::sys::fs::exists(Path))
    return llvm::Error::success();
  return writeTextFile(Path, Contents);
}

// The proof file 0.1 wrote for a goal it named so.
static std::string leanLegacyProofModule(llvm::StringRef Goal) {
  llvm::MD5 Hasher;
  llvm::MD5::MD5Result Hash;
  Hasher.update(Goal);
  Hasher.final(Hash);
  llvm::SmallString<32> Hex;
  llvm::MD5::stringifyResult(Hash, Hex);
  return "Goal_" + llvm::StringRef(Hex).take_front(16).str();
}

static constexpr llvm::StringLiteral LeanLegacyStubNote =
    "/- Complete this proof; this file is never regenerated. -/";

// Whether a proof file of 0.1 is still the stub 0.1 wrote.
static bool isLeanLegacyStub(llvm::StringRef Path) {
  auto Buffer = llvm::MemoryBuffer::getFile(Path);
  if (!Buffer)
    return false;
  llvm::StringRef Text = (*Buffer)->getBuffer();
  const llvm::StringRef Head =
      "import CppVerify.User\n\n/- Complete this proof; this file is never "
      "regenerated. -/\ntheorem ";
  if (!Text.consume_front(Head))
    return false;
  llvm::StringRef Goal = Text.take_until([](char C) { return C == ' '; });
  return Goal.consume_back("_proof") &&
         Text == Goal.str() + "_proof : " + Goal.str() + " := by\n  sorry\n";
}

static constexpr llvm::StringLiteral LeanProofMark = "/- cppverify proof\n";
static constexpr llvm::StringLiteral LeanQuarantineNote =
    "-- cpp-verify kept this proof here: ";

// What a proof file proves, from its header: a regeneration finds a proof
// by its goal's semantic hash wherever its function moved.
struct LeanProofRecord {
  std::string Path;
  std::string Goal;
  std::string Hash;
  std::string StableId;
  std::string BodyPrefix;
  /// The file cpp-verify wrote, never edited: a stub, or the proof
  /// cppverify_auto found. Nothing in it is the user's.
  bool Pristine = false;
  /// The proof cppverify_auto found.
  bool Automatic = false;
  /// What the header says automation made of the goal, and which revision
  /// of it.
  std::string Automation;
};

// The imports a proof file starts with: its function's goals, the user's
// lemmas, and the automation. Before 0.2's modules a proof imported only
// User (which imported every goal), and before cppverify_auto, not Auto.
enum class LeanProofImports { Modules, Automation, User };

// A proof starts from the goal's readable form, its names introduced.
static std::string
leanProofHead(llvm::StringRef Goal, llvm::StringRef Group,
              LeanProofImports Imports = LeanProofImports::Modules) {
  std::string Head;
  if (Imports == LeanProofImports::Modules)
    Head += "import CppVerify.Goals." + Group.str() + "\n";
  Head += "import CppVerify.User\n";
  if (Imports != LeanProofImports::User)
    Head += "import CppVerify.Auto\n";
  return Head + "\ntheorem " + Goal.str() + "_proof : " + Goal.str() +
         " := by\n  apply " + Goal.str() + ".of_readable\n";
}

static std::string leanProof(llvm::StringRef Goal, llvm::StringRef Group,
                             llvm::StringRef Intros, llvm::StringRef Last) {
  std::string Proof = leanProofHead(Goal, Group);
  if (!Intros.empty())
    Proof += "  intro " + Intros.str() + "\n";
  return Proof + "  " + Last.str() + "\n";
}

// Whether a proof is one cpp-verify wrote and nobody edited, and if so,
// whether cppverify_auto proves it: its last line is a stub's `sorry` or a
// step of cppverify_auto.
static std::optional<bool> leanGeneratedProof(llvm::StringRef Body,
                                              llvm::StringRef Goal,
                                              llvm::StringRef Group) {
  if (!llvm::any_of(
          std::initializer_list<LeanProofImports>{LeanProofImports::Modules,
                                                  LeanProofImports::Automation,
                                                  LeanProofImports::User},
          [&](LeanProofImports Imports) {
            return Body.consume_front(leanProofHead(Goal, Group, Imports));
          }))
    return std::nullopt;
  if (Body.consume_front("  intro ")) {
    const size_t End = Body.find('\n');
    if (End == llvm::StringRef::npos)
      return std::nullopt;
    Body = Body.drop_front(End + 1);
  }
  if (Body == "  sorry\n")
    return false;
  for (llvm::StringRef Step : LeanAutomationSteps)
    if (Body == ("  " + Step + "\n").str())
      return true;
  return std::nullopt;
}

// The revision of cppverify_auto that an automation note was written by.
// Names the printing of spec definitions and the prelude's tactic for their
// measures: a verdict an earlier revision kept is not used.
static constexpr llvm::StringLiteral LeanSpecRevision = "1";

static std::string leanAutomationTag() {
  return ("cppverify_auto " + LeanAutomationRevision + " ").str();
}

static std::string leanProofHeader(const LeanProjectGoal &Goal,
                                   llvm::StringRef Automation = "",
                                   bool Automatic = false) {
  std::string Header =
      LeanProofMark.str() + "   goal: " + Goal.Name +
      "\n   obligation: " + Goal.StableId + "\n   hash: " + Goal.Hash +
      "\n   bodies: " + Goal.BodyPrefix +
      "\n   source: " + (Goal.Source.empty() ? "unknown" : Goal.Source);
  if (!Automation.empty())
    Header += "\n   automation: " + Automation.str();
  return Header +
         (Automatic
              ? "\n   cppverify_auto proves this goal. cpp-verify rewrites "
                "this file only while it\n   is unedited; a proof you write "
                "here is yours, kept as any other. -/\n"
              : "\n   Complete this proof. Once you edit it, cpp-verify never "
                "rewrites it: it moves\n   it with its goal, and keeps it in "
                "Stale/ when no goal has its statement. -/\n");
}

static std::optional<LeanProofRecord> readLeanProof(llvm::StringRef Path) {
  auto Buffer = llvm::MemoryBuffer::getFile(Path);
  if (!Buffer)
    return std::nullopt;
  llvm::StringRef Text = (*Buffer)->getBuffer();
  if (!Text.consume_front(LeanProofMark))
    return std::nullopt;
  LeanProofRecord Record;
  Record.Path = Path.str();
  for (llvm::StringRef Rest = Text.take_front(Text.find("-/"));
       !Rest.empty();) {
    auto [Line, Next] = Rest.split('\n');
    Rest = Next;
    Line = Line.trim();
    if (Line.consume_front("goal: "))
      Record.Goal = Line.str();
    else if (Line.consume_front("obligation: "))
      Record.StableId = Line.str();
    else if (Line.consume_front("hash: "))
      Record.Hash = Line.str();
    else if (Line.consume_front("bodies: "))
      Record.BodyPrefix = Line.str();
    else if (Line.consume_front("automation: "))
      Record.Automation = Line.str();
  }
  if (Record.Goal.empty() || Record.Hash.empty())
    return std::nullopt;
  const size_t End = Text.find("-/\n");
  if (End != llvm::StringRef::npos)
    if (std::optional<bool> Automatic = leanGeneratedProof(
            Text.substr(End + 3), Record.Goal,
            llvm::sys::path::filename(llvm::sys::path::parent_path(Path)))) {
      Record.Pristine = true;
      Record.Automatic = *Automatic;
    }
  return Record;
}

static void replaceAllIn(std::string &Text, llvm::StringRef From,
                         llvm::StringRef To) {
  if (From.empty() || From == To)
    return;
  for (size_t At = Text.find(From); At != std::string::npos;
       At = Text.find(From, At + To.size()))
    Text.replace(At, From.size(), To.str());
}

// Moves a proof to its goal's file, its generated names renamed with it.
static llvm::Error moveLeanProof(llvm::StringRef From, llvm::StringRef To,
                                 const LeanProjectGoal &Goal,
                                 llvm::StringRef OldGoal,
                                 llvm::StringRef OldBodies,
                                 llvm::StringRef OldGroup = "") {
  auto Buffer = llvm::MemoryBuffer::getFile(From);
  if (!Buffer)
    return llvm::createStringError(
        Buffer.getError(), "cannot read Lean proof %s", From.str().c_str());
  llvm::StringRef Text = (*Buffer)->getBuffer();
  if (Text.consume_front(LeanProofMark)) {
    const size_t End = Text.find("-/\n");
    Text =
        End == llvm::StringRef::npos ? llvm::StringRef() : Text.substr(End + 3);
  }
  std::string Body;
  for (llvm::StringRef Rest = Text; !Rest.empty();) {
    auto [Line, Next] = Rest.split('\n');
    Rest = Next;
    if (Line.starts_with(LeanQuarantineNote) || Line == LeanLegacyStubNote)
      continue;
    Body += Line.str() + "\n";
  }
  replaceAllIn(Body, OldGoal, Goal.Name);
  replaceAllIn(Body, OldBodies, Goal.BodyPrefix);
  if (!OldGroup.empty())
    replaceAllIn(Body, ("import CppVerify.Goals." + OldGroup + "\n").str(),
                 "import CppVerify.Goals." + Goal.Group + "\n");
  if (std::error_code EC =
          llvm::sys::fs::create_directories(llvm::sys::path::parent_path(To)))
    return llvm::createStringError(EC, "cannot create %s", To.str().c_str());
  if (llvm::Error Error = writeTextFile(To, leanProofHeader(Goal) + Body))
    return Error;
  if (From != To)
    llvm::sys::fs::remove(From);
  return llvm::Error::success();
}

static llvm::Expected<std::string>
executeWithLogs(llvm::StringRef Program,
                const std::vector<std::string> &Arguments,
                llvm::StringRef LogBase) {
  std::vector<llvm::StringRef> ArgRefs;
  ArgRefs.reserve(Arguments.size());
  for (const std::string &Argument : Arguments)
    ArgRefs.push_back(Argument);
  const std::string StdoutPath = LogBase.str() + ".out";
  const std::string StderrPath = LogBase.str() + ".err";
  std::vector<std::optional<llvm::StringRef>> Redirects = {
      std::nullopt, StdoutPath, StderrPath};
  std::string ExecutionError;
  bool ExecutionFailed = false;
  const int ExitCode = llvm::sys::ExecuteAndWait(
      Program, ArgRefs, std::nullopt, Redirects, /*SecondsToWait=*/300,
      /*MemoryLimit=*/0, &ExecutionError, &ExecutionFailed);
  auto readLog = [](llvm::StringRef Path) {
    auto Buffer = llvm::MemoryBuffer::getFile(Path);
    return Buffer ? Buffer.get()->getBuffer().str() : std::string();
  };
  std::string Stdout = readLog(StdoutPath);
  std::string Stderr = readLog(StderrPath);
  llvm::sys::fs::remove(StdoutPath);
  llvm::sys::fs::remove(StderrPath);
  if (ExecutionFailed || ExitCode != 0) {
    std::string Message = ExecutionError;
    if (!Stdout.empty())
      Message += (Message.empty() ? "" : "\n") + Stdout;
    if (!Stderr.empty())
      Message += (Message.empty() ? "" : "\n") + Stderr;
    if (Message.size() > 4000)
      Message.resize(4000);
    return llvm::createStringError(llvm::inconvertibleErrorCode(),
                                   "command failed with exit code %d: %s",
                                   ExitCode, Message.c_str());
  }
  return Stdout;
}

// A Lean project: its generated modules, the proof file of each goal, the
// trial of cppverify_auto, and certification. Source verification and
// archive replay both write one through it; what it warns of is kept for
// the caller to report.
class LeanProject {
  const VerifyOptions &Opts;
  std::vector<std::string> Warnings;

  const std::string &leanProjectRoot() const {
    return Opts.LeanProjectPath.empty() ? Opts.LeanFallbackProjectPath
                                        : Opts.LeanProjectPath;
  }

public:
  explicit LeanProject(const VerifyOptions &Opts) : Opts(Opts) {}

  std::vector<std::string> takeWarnings() { return std::move(Warnings); }

  llvm::Error initializeLeanProject() {
    const std::string &Root = leanProjectRoot();
    std::error_code EC = llvm::sys::fs::create_directories(
        leanProjectPath(Root, {"CppVerify", "Proofs"}));
    if (EC)
      return llvm::createStringError(EC, "cannot create Lean project %s",
                                     Root.c_str());

    const std::string ToolchainPath = leanProjectPath(Root, {"lean-toolchain"});
    const std::string Toolchain = (LeanToolchain + "\n").str();
    if (llvm::sys::fs::exists(ToolchainPath)) {
      auto Existing = llvm::MemoryBuffer::getFile(ToolchainPath);
      if (!Existing)
        return llvm::createStringError(Existing.getError(),
                                       "cannot read Lean toolchain pin");
      const std::string Pin = Existing.get()->getBuffer().trim().str();
      if (Pin != LeanToolchain) {
        // A pin an earlier release wrote is moved with the release; any
        // other is the user's, and the generated semantics need ours.
        if (!llvm::is_contained(EarlierLeanToolchains, Pin))
          return llvm::createStringError(
              llvm::inconvertibleErrorCode(),
              "Lean project uses toolchain '%s'; expected '%s'", Pin.c_str(),
              LeanToolchain.str().c_str());
        if (llvm::Error Error = writeTextFile(ToolchainPath, Toolchain))
          return std::move(Error);
        Warnings.push_back("the Lean project " + Root + " pinned " + Pin +
                           ", which an earlier release of cpp-verify wrote; "
                           "it now pins " +
                           LeanToolchain.str() +
                           ", so a proof that no longer builds needs "
                           "updating for that Lean");
      }
    } else if (llvm::Error Error = writeTextFile(ToolchainPath, Toolchain)) {
      return std::move(Error);
    }

    constexpr llvm::StringLiteral Lakefile =
        "name = \"cppverify_proof\"\n"
        "version = \"0.1.0\"\n"
        "defaultTargets = [\"CppVerify\"]\n\n"
        "[[lean_lib]]\n"
        "name = \"CppVerify\"\n";
    if (llvm::Error Error = writeTextFileIfMissing(
            leanProjectPath(Root, {"lakefile.toml"}), Lakefile))
      return std::move(Error);

    // A project of an earlier release imports CppVerify.Generated here,
    // which still imports every goal.
    constexpr llvm::StringLiteral UserFile =
        "import CppVerify.Specs\n\n"
        "/- Add reusable lemmas here. This file is never regenerated. -/\n";
    if (llvm::Error Error = writeTextFileIfMissing(
            leanProjectPath(Root, {"CppVerify", "User.lean"}), UserFile))
      return Error;

    std::string Prelude = std::string(LeanGeneratedNote) + "\n\n";
    llvm::raw_string_ostream PreludeOS(Prelude);
    emitLeanPrelude(PreludeOS, /*Project=*/true);
    for (const auto &[File, Contents] :
         {std::pair<llvm::StringRef, llvm::StringRef>{"Prelude.lean", Prelude},
          {"Auto.lean", LeanAutomationSource}})
      if (llvm::Error Error = writeTextFileIfChanged(
              leanProjectPath(Root, {"CppVerify", File}), Contents))
        return Error;
    // The root of the library, so that `lake build` builds every proof.
    return writeTextFileIfChanged(leanProjectPath(Root, {"CppVerify.lean"}),
                                  "import CppVerify.Check\n");
  }

  // The generated modules of a run: Specs, a goal module for each function
  // the run exported, and Generated, which imports them all. Any other goal
  // module is removed, so that every module of the project builds: one an
  // earlier run wrote may apply a spec Specs no longer declares, as after a
  // fallback run whose solver settled the functions that applied it. The
  // proofs of a function the run did not export stay as they are.
  llvm::Error writeLeanProjectModules(const LeanProjectModules &Modules) {
    const std::string &Root = leanProjectRoot();
    const std::string Header = std::string(LeanGeneratedNote) + "\n";
    if (llvm::Error Error = writeTextFileIfChanged(
            leanProjectPath(Root, {"CppVerify", "Specs.lean"}),
            Header +
                "import CppVerify.Prelude\n\nnoncomputable section\n\n"
                "attribute [local instance] cppVerifyPropDecidable\n\n" +
                leanSpecsText(Modules)))
      return Error;
    const std::string GoalsDir = leanProjectPath(Root, {"CppVerify", "Goals"});
    if (std::error_code EC = llvm::sys::fs::create_directories(GoalsDir))
      return llvm::createStringError(EC, "cannot create %s", GoalsDir.c_str());
    std::string Generated = Header + "import CppVerify.Prelude\n"
                                     "import CppVerify.Specs\n";
    for (const std::string &Group : Modules.Order) {
      if (llvm::Error Error = writeTextFileIfChanged(
              leanProjectPath(GoalsDir, {Group + ".lean"}),
              Header + "import CppVerify.Specs\n\n" +
                  LeanGoalModulePreamble.str() + Modules.Goals.at(Group)))
        return Error;
      Generated += "import CppVerify.Goals." + Group + "\n";
    }
    if (llvm::Error Error = writeTextFileIfChanged(
            leanProjectPath(Root, {"CppVerify", "Generated.lean"}), Generated))
      return Error;

    std::error_code EC;
    for (llvm::sys::fs::directory_iterator It(GoalsDir, EC), End;
         It != End && !EC; It.increment(EC))
      if (llvm::sys::path::extension(It->path()) == ".lean" &&
          !Modules.Goals.count(llvm::sys::path::stem(It->path()).str()))
        llvm::sys::fs::remove(It->path());
    return llvm::Error::success();
  }

  // The refutation of each certified failure of the run,
  // Refutations/<group>/<goal>.lean. Any other is removed: its failure is
  // gone, or its program is not this one.
  llvm::Error
  writeLeanRefutations(const std::vector<LeanRefutation> &Refutations) {
    const std::string Dir =
        leanProjectPath(leanProjectRoot(), {"CppVerify", "Refutations"});
    std::set<std::string> Written;
    for (const LeanRefutation &Refutation : Refutations) {
      const std::string Path =
          leanProjectPath(Dir, {Refutation.Group, Refutation.Goal + ".lean"});
      if (std::error_code EC = llvm::sys::fs::create_directories(
              llvm::sys::path::parent_path(Path)))
        return llvm::createStringError(EC, "cannot create %s", Path.c_str());
      if (llvm::Error Error = writeTextFileIfChanged(
              Path, std::string(LeanGeneratedNote) + "\n" + Refutation.Text))
        return Error;
      Written.insert(Path);
    }
    std::error_code EC;
    std::vector<std::string> Gone;
    for (llvm::sys::fs::recursive_directory_iterator It(Dir, EC), End;
         It != End && !EC; It.increment(EC))
      if (llvm::sys::path::extension(It->path()) == ".lean" &&
          !Written.count(It->path()))
        Gone.push_back(It->path());
    for (const std::string &Path : Gone) {
      llvm::sys::fs::remove(Path);
      llvm::sys::fs::remove(llvm::sys::path::parent_path(Path));
    }
    if (Written.empty())
      llvm::sys::fs::remove(Dir);
    return llvm::Error::success();
  }

  static std::vector<llvm::StringRef>
  leanProofComponents(const LeanProjectGoal &Goal, std::string &File) {
    File = Goal.Name + ".lean";
    return {"CppVerify", "Proofs", Goal.Group, File};
  }

  // Each goal gets its proof file: the one recorded with its semantic hash,
  // which follows it when its function is renamed or moved; else the one
  // 0.1 wrote for it; else a stub. A proof no goal takes is kept in Stale/,
  // where a goal with its statement takes it back. A fallback run examines
  // only the functions its solver leaves unresolved (RunGroups names the
  // groups it gave the solver), so it leaves the proofs of the others alone.
  llvm::Error
  finalizeLeanProject(const std::vector<LeanProjectGoal> &ProjectGoals,
                      const std::set<std::string> *RunGroups) {
    const std::string &Root = leanProjectRoot();
    const std::string ProofsDir =
        leanProjectPath(Root, {"CppVerify", "Proofs"});
    const std::string StaleDir = leanProjectPath(Root, {"Stale"});
    std::map<std::string, const LeanProjectGoal *> Goals, Known;
    std::set<std::string> Examined;
    std::map<std::string, std::string> StableGoal;
    for (const LeanProjectGoal &Goal : ProjectGoals) {
      (Goal.Exported ? Goals : Known).emplace(Goal.Name, &Goal);
      Examined.insert(Goal.Group);
      if (Goal.Exported)
        StableGoal.emplace(Goal.StableId, Goal.Name);
    }

    // Recorded proofs, live first, then kept ones, each in path order.
    std::vector<LeanProofRecord> Records;
    std::set<std::string> Legacy;
    for (const std::string &Dir : {ProofsDir, StaleDir}) {
      std::error_code EC;
      std::vector<std::string> Paths;
      for (llvm::sys::fs::recursive_directory_iterator It(Dir, EC), End;
           It != End && !EC; It.increment(EC))
        if (llvm::sys::path::extension(It->path()) == ".lean")
          Paths.push_back(It->path());
      llvm::sort(Paths);
      for (const std::string &Path : Paths)
        if (std::optional<LeanProofRecord> Record = readLeanProof(Path))
          Records.push_back(std::move(*Record));
        else if (Dir == ProofsDir &&
                 llvm::sys::path::parent_path(Path) == ProofsDir &&
                 llvm::sys::path::filename(Path).starts_with("Goal_"))
          Legacy.insert(Path);
    }
    auto groupOf = [](const LeanProofRecord &Record) {
      return llvm::sys::path::filename(
                 llvm::sys::path::parent_path(Record.Path))
          .str();
    };
    // A proof of a goal this run knows but does not export, or of a
    // function it left to the solver, stays where it is.
    auto unexamined = [&](const LeanProofRecord &Record) {
      auto Goal = Known.find(Record.Goal);
      if (Goal != Known.end() && Goal->second->Hash == Record.Hash)
        return true;
      const std::string Group = groupOf(Record);
      return RunGroups && RunGroups->count(Group) && !Examined.count(Group);
    };
    std::set<std::string> Taken;
    // Directories a proof left, removed at the end if nothing is left in them.
    std::set<std::string> Emptied;
    auto relative = [&](llvm::StringRef Path) {
      llvm::StringRef Rel = Path;
      Rel.consume_front(Root);
      return Rel.ltrim("/\\").str();
    };
    // A renamed function's goals move together: for each goal's group, how
    // many of its goals a group that is gone has a proof of.
    auto gone = [&](const LeanProofRecord &Record) {
      return !Goals.count(Record.Goal) && !unexamined(Record) &&
             !Record.Pristine;
    };
    std::map<std::pair<std::string, std::string>, unsigned> Affinity;
    for (const auto &[Name, Goal] : Goals) {
      std::set<std::string> From;
      for (const LeanProofRecord &Record : Records)
        if (Record.Hash == Goal->Hash && gone(Record) &&
            From.insert(groupOf(Record)).second)
          ++Affinity[{Goal->Group, groupOf(Record)}];
    }
    std::string CheckFile;
    for (const auto &[Name, Goal] : Goals) {
      std::string File;
      const std::string ProofPath =
          leanProjectPath(Root, leanProofComponents(*Goal, File));
      auto Here = llvm::find_if(Records, [&](const LeanProofRecord &Record) {
        return Record.Path == ProofPath && Record.Hash == Goal->Hash;
      });
      // Its own proof first, wherever it is kept; then one written for a
      // goal that is gone, from the group with proofs of the most goals of
      // this one (the function renamed), in path order within it.
      auto Moving = llvm::find_if(Records, [&](const LeanProofRecord &Record) {
        return Record.Hash == Goal->Hash && !Taken.count(Record.Path) &&
               Record.Goal == Name && !Record.Pristine;
      });
      auto affinity = [&](const LeanProofRecord &Record) {
        return Affinity[{Goal->Group, groupOf(Record)}];
      };
      if (Moving == Records.end())
        for (auto It = Records.begin(); It != Records.end(); ++It)
          if (It->Hash == Goal->Hash && !Taken.count(It->Path) && gone(*It) &&
              (Moving == Records.end() || affinity(*It) > affinity(*Moving)))
            Moving = It;
      const std::string LegacyPath = leanProjectPath(
          Root, {"CppVerify", "Proofs",
                 leanLegacyProofModule(Goal->LegacyName) + ".lean"});
      if (Here != Records.end()) {
        Taken.insert(Here->Path);
      } else if (Moving != Records.end() &&
                 (Moving->Path != ProofPath || !Taken.count(ProofPath))) {
        const bool WasKept =
            llvm::StringRef(Moving->Path).starts_with(StaleDir);
        if (llvm::Error Error =
                moveLeanProof(Moving->Path, ProofPath, *Goal, Moving->Goal,
                              Moving->BodyPrefix, groupOf(*Moving)))
          return Error;
        Warnings.push_back("the Lean proof of " + Goal->StableId +
                           (WasKept ? " came back from " : " moved from ") +
                           relative(Moving->Path) + " to " +
                           relative(ProofPath) +
                           ", the file of the goal with its statement");
        Taken.insert(Moving->Path);
        Taken.insert(ProofPath);
        Emptied.insert(llvm::sys::path::parent_path(Moving->Path).str());
      } else if (Legacy.count(LegacyPath)) {
        const bool Stub = isLeanLegacyStub(LegacyPath);
        if (llvm::Error Error =
                moveLeanProof(LegacyPath, ProofPath, *Goal, Goal->LegacyName,
                              Goal->LegacyBodyPrefix))
          return Error;
        if (!Stub)
          Warnings.push_back("the Lean proof " + relative(LegacyPath) +
                             " that cpp-verify 0.1 wrote for " +
                             Goal->StableId + " is now " + relative(ProofPath));
        Legacy.erase(LegacyPath);
        Taken.insert(ProofPath);
      } else if (llvm::sys::fs::exists(ProofPath)) {
        // A proof written over its stub: its header lets it follow its
        // goal from now on.
        if (!readLeanProof(ProofPath))
          if (llvm::Error Error =
                  moveLeanProof(ProofPath, ProofPath, *Goal, Name, ""))
            return Error;
        Taken.insert(ProofPath);
      } else {
        if (std::error_code EC = llvm::sys::fs::create_directories(
                llvm::sys::path::parent_path(ProofPath)))
          return llvm::createStringError(EC, "cannot create %s",
                                         ProofPath.c_str());
        if (llvm::Error Error =
                writeTextFile(ProofPath, leanProofHeader(*Goal) +
                                             leanProof(Goal->Name, Goal->Group,
                                                       Goal->Intros, "sorry")))
          return Error;
        Taken.insert(ProofPath);
      }
      CheckFile +=
          "import CppVerify.Proofs." + Goal->Group + "." + Goal->Name + "\n";
    }

    // What no goal took is kept, with why.
    auto keep = [&](llvm::StringRef Path,
                    const std::string &Why) -> llvm::Error {
      llvm::SmallString<256> Kept(StaleDir);
      llvm::sys::path::append(Kept, llvm::StringRef(relative(Path))
                                        .drop_front(std::strlen("CppVerify/")));
      std::string Target = std::string(Kept);
      for (unsigned Copy = 2; llvm::sys::fs::exists(Target); ++Copy)
        Target = std::string(Kept) + "." + std::to_string(Copy);
      if (std::error_code EC = llvm::sys::fs::create_directories(
              llvm::sys::path::parent_path(Target)))
        return llvm::createStringError(EC, "cannot create %s", Target.c_str());
      if (std::error_code EC = llvm::sys::fs::rename(Path, Target))
        return llvm::createStringError(EC, "cannot keep %s",
                                       Path.str().c_str());
      std::error_code EC;
      llvm::raw_fd_ostream Note(Target, EC, llvm::sys::fs::OF_Append);
      if (!EC)
        Note << "\n" << LeanQuarantineNote << Why << "\n";
      Warnings.push_back("the Lean proof " + relative(Path) + " is kept in " +
                         relative(Target) + ": " + Why);
      return llvm::Error::success();
    };
    for (const LeanProofRecord &Record : Records) {
      if (Taken.count(Record.Path) ||
          llvm::StringRef(Record.Path).starts_with(StaleDir) ||
          unexamined(Record))
        continue;
      Emptied.insert(llvm::sys::path::parent_path(Record.Path).str());
      if (Record.Pristine) {
        llvm::sys::fs::remove(Record.Path);
        continue;
      }
      auto Same = StableGoal.find(Record.StableId);
      std::string Why =
          Same != StableGoal.end()
              ? "the statement of " + Record.StableId +
                    " changed; its goal is now " + Same->second
          : Examined.count(groupOf(Record))
              ? "its function has no obligation with this statement any more"
              : "its function is gone, and no goal has its statement";
      if (llvm::Error Error = keep(Record.Path, Why))
        return Error;
    }
    for (const std::string &Path : Legacy)
      if (isLeanLegacyStub(Path))
        llvm::sys::fs::remove(Path);
      else if (llvm::Error Error =
                   keep(Path, "a proof cpp-verify 0.1 wrote for a goal this "
                              "source no longer has"))
        return Error;
    for (std::string Dir : Emptied)
      while (Dir != ProofsDir && Dir != Root && !llvm::sys::fs::remove(Dir))
        Dir = llvm::sys::path::parent_path(Dir).str();

    if (Opts.LeanPruneStale && llvm::sys::fs::exists(StaleDir)) {
      unsigned Pruned = 0;
      std::error_code EC;
      for (llvm::sys::fs::recursive_directory_iterator It(StaleDir, EC), End;
           It != End && !EC; It.increment(EC))
        if (llvm::sys::path::extension(It->path()) == ".lean" ||
            llvm::StringRef(It->path()).contains(".lean."))
          ++Pruned;
      if (std::error_code EC = llvm::sys::fs::remove_directories(StaleDir))
        return llvm::createStringError(EC, "cannot remove %s",
                                       StaleDir.c_str());
      Warnings.push_back(
          "removed " +
          (Pruned == 1 ? std::string("the Lean proof")
                       : "the " + std::to_string(Pruned) + " Lean proofs") +
          " kept in Stale/, as --lean-prune-stale asks");
    }

    CheckFile += "\n";
    for (const auto &[Name, Goal] : Goals) {
      CheckFile += "example : " + Name + " := " + Name + "_proof\n";
      CheckFile += "#print axioms " + Name + "_proof\n";
    }
    return writeTextFileIfChanged(
        leanProjectPath(Root, {"CppVerify", "Check.lean"}), CheckFile);
  }

  // Certifies each goal's proof: an error fails every goal; otherwise the
  // goals whose proofs fail, each with why. A proof's own module must build
  // without `sorry`; then the certifier (LeanCertifier.h) checks the compiled
  // modules, which nothing in the user's source can change.
  // How many Lean processes to run at once for Tasks of them.
  unsigned leanJobs(size_t Tasks) const {
    const unsigned Jobs =
        Opts.LeanJobs
            ? Opts.LeanJobs
            : llvm::heavyweight_hardware_concurrency().compute_thread_count();
    return std::max<size_t>(1, std::min<size_t>(Tasks, Jobs));
  }

  // How lake runs the Lean the project pins. elan picks a toolchain by the
  // working directory, not by --dir, so its proxy is given the pin; and
  // whatever runs, lake must report the pinned Lean.
  struct LeanLauncher {
    std::string Lake;
    std::vector<std::string> Prefix;
    std::string LogBase;

    llvm::Expected<std::string> run(std::vector<std::string> Arguments,
                                    llvm::StringRef Stage,
                                    llvm::StringRef Root) const {
      std::vector<std::string> Command = Prefix;
      Command.push_back("--dir=" + Root.str());
      Command.insert(Command.end(), std::make_move_iterator(Arguments.begin()),
                     std::make_move_iterator(Arguments.end()));
      return executeWithLogs(Lake, Command, LogBase + "-" + Stage.str());
    }
  };

  llvm::Expected<LeanLauncher> leanLauncher(llvm::StringRef Purpose) {
    auto Lake = llvm::sys::findProgramByName("lake");
    if (!Lake)
      return llvm::createStringError(Lake.getError(),
                                     "cannot find the Lean project launcher");
    LeanLauncher Launcher{
        *Lake, {"lake"}, leanProjectPath(leanProjectRoot(), {Purpose})};
    auto Elan = llvm::sys::findProgramByName("elan");
    bool ViaElan = false;
    if (!Elan || llvm::sys::fs::equivalent(*Lake, *Elan, ViaElan))
      ViaElan = false;
    if (ViaElan)
      Launcher.Prefix.push_back(("+" + LeanToolchain).str());

    // lake takes --version alone.
    std::vector<std::string> Query = Launcher.Prefix;
    Query.push_back("--version");
    auto Reported =
        executeWithLogs(*Lake, Query, Launcher.LogBase + "-version");
    if (!Reported)
      return Reported.takeError();
    const llvm::StringRef Pinned =
        LeanToolchain.substr(LeanToolchain.find(":v") + 2);
    llvm::StringRef Version = *Reported;
    if (size_t At = Version.find("Lean version "); At != llvm::StringRef::npos)
      Version =
          Version.substr(At + std::strlen("Lean version "))
              .take_while([](char C) { return llvm::isDigit(C) || C == '.'; });
    else
      Version = "";
    if (Version != Pinned)
      return llvm::createStringError(
          llvm::inconvertibleErrorCode(),
          "the project pins %s, but %s runs Lean %s; install elan "
          "(https://github.com/leanprover/elan), which runs the pinned "
          "toolchain",
          LeanToolchain.str().c_str(), Lake->c_str(),
          Version.empty() ? "of an unknown version" : Version.str().c_str());
    return Launcher;
  }

  // The specs of a project as Specs.lean declares them: each recursion group
  // by its real definitions where Lean accepts them, callees first, and
  // opaque where it does not, where a member has no definition, or where no
  // Lean is installed to try them. Lean's verdict on a group's text, with
  // what its callees are, is kept in .cppverify/specs, so that the file is
  // the same on every run. A group is tried with its undecided callees real
  // and keeps its verdict only if they are; else it is tried again with the
  // rejected callees opaque.
  std::string leanSpecsText(const LeanProjectModules &Modules) {
    const auto &Specs = Modules.Specs;
    // Strongly connected components of the calls, callees first (Tarjan).
    std::vector<std::vector<std::string>> Groups;
    std::map<std::string, size_t> GroupOf;
    {
      std::map<std::string, unsigned> Index, Low;
      std::set<std::string> OnStack;
      std::vector<std::string> Stack;
      unsigned Counter = 0;
      std::function<void(const std::string &)> visit =
          [&](const std::string &V) {
            Index[V] = Low[V] = Counter++;
            Stack.push_back(V);
            OnStack.insert(V);
            for (const std::string &W : Specs.at(V).Applies) {
              if (!Specs.count(W))
                continue;
              if (!Index.count(W)) {
                visit(W);
                Low[V] = std::min(Low[V], Low[W]);
              } else if (OnStack.count(W)) {
                Low[V] = std::min(Low[V], Index[W]);
              }
            }
            if (Low[V] != Index[V])
              return;
            std::vector<std::string> Group;
            std::string W;
            do {
              W = Stack.back();
              Stack.pop_back();
              OnStack.erase(W);
              Group.push_back(W);
              GroupOf[W] = Groups.size();
            } while (W != V);
            std::sort(Group.begin(), Group.end());
            Groups.push_back(std::move(Group));
          };
      for (const auto &[Identity, Declaration] : Specs)
        if (!Index.count(Identity))
          visit(Identity);
    }
    std::vector<std::set<size_t>> Callees(Groups.size());
    std::vector<std::string> Definition(Groups.size());
    // 1 real, 0 opaque, -1 undecided.
    std::vector<int> Verdict(Groups.size(), -1);
    for (size_t G = 0; G != Groups.size(); ++G) {
      for (const std::string &Member : Groups[G]) {
        const LeanSpecDeclaration &Declaration = Specs.at(Member);
        if (Declaration.Definition.empty())
          Verdict[G] = 0;
        Definition[G] += Declaration.Definition;
        for (const std::string &Callee : Declaration.Applies)
          if (Specs.count(Callee) && GroupOf.at(Callee) != G)
            Callees[G].insert(GroupOf.at(Callee));
      }
      if (Groups[G].size() > 1)
        Definition[G] = "mutual\n" + Definition[G] + "end\n\n";
    }
    auto opaque = [&](size_t G) {
      std::string Text;
      for (const std::string &Member : Groups[G])
        Text += Specs.at(Member).Opaque;
      return Text;
    };
    // What a group's verdict rests on: the toolchain, this revision of the
    // printer and the prelude's tactic, its text, and what its callees are.
    auto keyOf = [&](size_t G, const std::set<size_t> &Assumed) {
      llvm::SHA256 Hasher;
      Hasher.update(LeanToolchain);
      Hasher.update(LeanSpecRevision);
      Hasher.update(Definition[G]);
      for (size_t C : Callees[G])
        Hasher.update(Groups[C].front() + (Verdict[C] == 1 || Assumed.count(C)
                                               ? "=real"
                                               : "=opaque"));
      return llvm::toHex(Hasher.final());
    };
    const std::string &Root = leanProjectRoot();
    const std::string Dir = leanProjectPath(Root, {".cppverify", "specs"});
    std::optional<LeanLauncher> Launcher;
    bool LeanUnavailable = false;
    for (size_t Round = 0; Round <= Groups.size(); ++Round) {
      std::set<size_t> Trying;
      std::map<size_t, std::string> Keys;
      for (size_t G = 0; G != Groups.size(); ++G) {
        if (Verdict[G] >= 0)
          continue;
        const bool CalleesDecided =
            llvm::all_of(Callees[G], [&](size_t C) { return Verdict[C] >= 0; });
        const std::string Key = keyOf(G, Trying);
        if (CalleesDecided)
          if (auto Kept =
                  llvm::MemoryBuffer::getFile(leanProjectPath(Dir, {Key}))) {
            Verdict[G] = (*Kept)->getBuffer().trim() == "real" ? 1 : 0;
            continue;
          }
        if (LeanUnavailable) {
          Verdict[G] = 0;
          continue;
        }
        Trying.insert(G);
        Keys[G] = Key;
      }
      if (Trying.empty())
        break;
      std::map<std::string, std::string> Axioms;
      if (!tryLeanSpecs(Specs, Groups, Definition, Verdict, Trying, Launcher,
                        opaque, Axioms)) {
        LeanUnavailable = true;
        for (size_t G : Trying)
          Verdict[G] = 0;
        break;
      }
      std::map<size_t, bool> Accepted;
      for (size_t G : Trying)
        Accepted[G] = llvm::all_of(Groups[G], [&](const std::string &Member) {
          auto It = Axioms.find(Specs.at(Member).Name);
          if (It == Axioms.end() || It->second == "missing")
            return false;
          llvm::SmallVector<llvm::StringRef, 4> Used;
          llvm::StringRef(It->second).split(Used, ',', -1, false);
          return llvm::all_of(Used, [](llvm::StringRef Axiom) {
            return Axiom == "propext" || Axiom == "Quot.sound" ||
                   Axiom == "Classical.choice";
          });
        });
      // A callee decided before this round was what the trial assumed; one
      // tried in it was assumed real.
      for (size_t G : Trying) {
        if (!llvm::all_of(Callees[G], [&](size_t C) {
              return !Trying.count(C) || Accepted[C];
            }))
          continue;
        Verdict[G] = Accepted[G] ? 1 : 0;
        if (!llvm::sys::fs::create_directories(Dir))
          llvm::consumeError(
              writeTextFile(leanProjectPath(Dir, {Keys[G]}),
                            Accepted[G] ? "real\n" : "opaque\n"));
      }
    }
    std::string Text;
    for (size_t G = 0; G != Groups.size(); ++G)
      Text += Verdict[G] == 1 ? Definition[G] : opaque(G);
    return Text;
  }

  // Elaborates the spec groups of Trying with the others as decided, in a
  // file of their own, and reports the axioms of each member of Trying: a
  // definition Lean rejects is added with sorryAx, or not at all. False when
  // no pinned Lean can run it.
  bool tryLeanSpecs(const std::map<std::string, LeanSpecDeclaration> &Specs,
                    const std::vector<std::vector<std::string>> &Groups,
                    const std::vector<std::string> &Definition,
                    const std::vector<int> &Verdict,
                    const std::set<size_t> &Trying,
                    std::optional<LeanLauncher> &Launcher,
                    llvm::function_ref<std::string(size_t)> Opaque,
                    std::map<std::string, std::string> &Axioms) {
    const std::string &Root = leanProjectRoot();
    if (!Launcher) {
      auto Found = leanLauncher(".cppverify-specs");
      if (!Found) {
        llvm::consumeError(Found.takeError());
        return false;
      }
      if (auto Build = Found->run({"build", "CppVerify.Auto"}, "build", Root);
          !Build) {
        llvm::consumeError(Build.takeError());
        return false;
      }
      Launcher = std::move(*Found);
    }
    const std::string Dir = leanProjectPath(Root, {".cppverify", "specs"});
    if (llvm::sys::fs::create_directories(Dir))
      return false;
    const std::string Source = leanProjectPath(Dir, {"trial.lean"});
    const std::string Report = leanProjectPath(Dir, {"trial.report"});
    std::string Quoted = "\"";
    for (char C : Report) {
      if (C == '\\' || C == '"')
        Quoted += '\\';
      Quoted += C;
    }
    Quoted += "\"";
    std::string Text = "import CppVerify.Auto\n\n#eval CppVerify.Auto.report " +
                       Quoted +
                       " \"ready\"\n\nnoncomputable section\n\n"
                       "attribute [local instance] cppVerifyPropDecidable\n\n";
    for (size_t G = 0; G != Groups.size(); ++G) {
      if (Verdict[G] == 1 || Trying.count(G))
        Text += Definition[G];
      else
        Text += Opaque(G);
      if (Trying.count(G))
        for (const std::string &Member : Groups[G])
          Text += "#cppverify_axioms " + Quoted + " " + Specs.at(Member).Name +
                  "\n\n";
    }
    llvm::sys::fs::remove(Report);
    if (llvm::Error Error = writeTextFile(Source, Text)) {
      llvm::consumeError(std::move(Error));
      return false;
    }
    // Lean exits with an error status when a definition fails; the report
    // says which.
    if (auto Run = Launcher->run({"env", "lean", "-DmaxErrors=1000000", Source},
                                 "specs", Root);
        !Run)
      llvm::consumeError(Run.takeError());
    auto Buffer = llvm::MemoryBuffer::getFile(Report);
    if (!Buffer)
      return false;
    bool Ready = false;
    for (llvm::StringRef Rest = (*Buffer)->getBuffer(); !Rest.empty();) {
      auto [Line, Next] = Rest.split('\n');
      Rest = Next;
      Line = Line.rtrim("\r");
      if (Line == "ready") {
        Ready = true;
        continue;
      }
      llvm::SmallVector<llvm::StringRef, 3> Fields;
      Line.split(Fields, '\t', 2);
      if (Fields.size() == 3 && Fields[0] == "axioms")
        Axioms[Fields[1].str()] = Fields[2].str();
    }
    return Ready;
  }

  // What a proof is built from: the pinned toolchain, its source, and the
  // compiled modules of the project in its import closure, read from the
  // import lines of their sources. None when a module of the closure has no
  // compiled module.
  std::optional<std::string> leanProofKey(llvm::StringRef ProofSource) {
    const std::string &Root = leanProjectRoot();
    auto importsOf = [](llvm::StringRef Source) {
      std::vector<std::string> Imports;
      if (auto Buffer = llvm::MemoryBuffer::getFile(Source))
        for (llvm::StringRef Rest = (*Buffer)->getBuffer(); !Rest.empty();) {
          auto [Line, Next] = Rest.split('\n');
          Rest = Next;
          if (Line.consume_front("import "))
            Imports.push_back(Line.trim().str());
        }
      return Imports;
    };
    llvm::SHA256 Hasher;
    Hasher.update(LeanToolchain);
    auto Source = llvm::MemoryBuffer::getFile(ProofSource);
    if (!Source)
      return std::nullopt;
    Hasher.update((*Source)->getBuffer());
    std::map<std::string, std::string> Compiled;
    std::vector<std::string> Work = importsOf(ProofSource);
    while (!Work.empty()) {
      const std::string Module = Work.back();
      Work.pop_back();
      if (Compiled.count(Module))
        continue;
      std::string Relative = Module;
      std::replace(Relative.begin(), Relative.end(), '.', '/');
      const std::string ModuleSource =
          leanProjectPath(Root, {Relative + ".lean"});
      if (!llvm::sys::fs::exists(ModuleSource))
        continue;
      auto Object = llvm::MemoryBuffer::getFile(leanProjectPath(
          Root, {".lake", "build", "lib", "lean", Relative + ".olean"}));
      if (!Object)
        return std::nullopt;
      Compiled[Module] = llvm::toHex(llvm::SHA256::hash(
          llvm::arrayRefFromStringRef((*Object)->getBuffer())));
      for (std::string &Import : importsOf(ModuleSource))
        Work.push_back(std::move(Import));
    }
    for (const auto &[Module, Hash] : Compiled) {
      Hasher.update(Module);
      Hasher.update(Hash);
    }
    return llvm::toHex(Hasher.final());
  }

  llvm::Expected<std::map<std::string, std::string>>
  certifyLeanProject(const std::vector<LeanProjectGoal> &ProjectGoals,
                     const std::vector<LeanRefutation> &Refutations = {}) {
    if (ProjectGoals.empty() && Refutations.empty())
      return llvm::createStringError(llvm::inconvertibleErrorCode(),
                                     "the project has no proof obligations");
    auto Launcher = leanLauncher(".cppverify-certification");
    if (!Launcher)
      return Launcher.takeError();
    const std::string &Root = leanProjectRoot();
    auto runLake = [&](std::vector<std::string> Arguments,
                       llvm::StringRef Stage) {
      return Launcher->run(std::move(Arguments), Stage, Root);
    };

    if (auto Build = runLake({"build", "CppVerify.Generated", "CppVerify.User",
                              "CppVerify.Auto"},
                             "build");
        !Build)
      return Build.takeError();

    const std::string ProofBuildDir = leanProjectPath(
        Root, {".lake", "build", "lib", "lean", "CppVerify", "Proofs"});
    if (std::error_code EC = llvm::sys::fs::create_directories(ProofBuildDir))
      return llvm::createStringError(
          EC, "cannot create Lean proof build directory");

    std::map<std::string, const LeanProjectGoal *> UniqueGoals;
    for (const LeanProjectGoal &Goal : ProjectGoals)
      UniqueGoals.emplace(Goal.Name, &Goal);
    // What is built: each goal's proof, and each refutation, which is its
    // goal's module too; with the certifier's line for each, and the name
    // it reports.
    struct Build {
      std::string Name, Source, Object, Entry;
    };
    std::vector<Build> Proofs;
    for (const auto &[Name, Goal] : UniqueGoals) {
      std::string File;
      Proofs.push_back(
          {Name, leanProjectPath(Root, leanProofComponents(*Goal, File)),
           leanProjectPath(leanProjectPath(ProofBuildDir, {Goal->Group}),
                           {Name + ".olean"}),
           Name + "\tCppVerify.Proofs." + Goal->Group + "." + Name +
               "\tCppVerify.Goals." + Goal->Group + "\n"});
    }
    for (const LeanRefutation &Refutation : Refutations) {
      const std::string Module =
          "CppVerify.Refutations." + Refutation.Group + "." + Refutation.Goal;
      Proofs.push_back(
          {Refutation.Goal + "_refuted",
           leanProjectPath(Root, {"CppVerify", "Refutations", Refutation.Group,
                                  Refutation.Goal + ".lean"}),
           leanProjectPath(Root, {".lake", "build", "lib", "lean", "CppVerify",
                                  "Refutations", Refutation.Group,
                                  Refutation.Goal + ".olean"}),
           Refutation.Goal + "\t" + Module + "\t" + Module + "\trefutation\n"});
    }
    for (const Build &Proof : Proofs)
      if (std::error_code EC = llvm::sys::fs::create_directories(
              llvm::sys::path::parent_path(Proof.Object)))
        return llvm::createStringError(
            EC, "cannot create Lean proof build directory");
    // Each proof builds by itself, several at once, unless nothing it is
    // built from changed since it last built: its source and the compiled
    // modules of the project it imports (which Lake has just built). Lake
    // cannot say this itself: a module whose import failed is not built and
    // not named, and its .olean of an earlier build would stay.
    const std::string KeyDir = leanProjectPath(Root, {".cppverify", "built"});
    if (std::error_code EC = llvm::sys::fs::create_directories(KeyDir))
      return llvm::createStringError(EC, "cannot create %s", KeyDir.c_str());
    std::vector<std::optional<std::string>> BuildErrors(Proofs.size());
    std::atomic<size_t> NextProof{0};
    auto buildProofs = [&] {
      for (size_t I; (I = NextProof++) < Proofs.size();) {
        const std::string &Name = Proofs[I].Name;
        const std::string &ProofSource = Proofs[I].Source;
        const std::string &ProofObject = Proofs[I].Object;
        const std::string KeyFile = leanProjectPath(KeyDir, {Name});
        const std::optional<std::string> Key = leanProofKey(ProofSource);
        if (Key && llvm::sys::fs::exists(ProofObject))
          if (auto Kept = llvm::MemoryBuffer::getFile(KeyFile))
            if ((*Kept)->getBuffer() == *Key)
              continue;
        llvm::sys::fs::remove(ProofObject);
        llvm::sys::fs::remove(KeyFile);
        if (auto Proof = runLake({"env", "lean", "-EhasSorry", "-R", Root, "-o",
                                  ProofObject, ProofSource},
                                 Name);
            !Proof)
          BuildErrors[I] =
              llvm::StringRef(llvm::toString(Proof.takeError())).rtrim().str();
        else if (Key)
          llvm::consumeError(writeTextFile(KeyFile, *Key));
      }
    };
    {
      std::vector<std::thread> Builders;
      for (unsigned J = 0, E = leanJobs(Proofs.size()); J != E; ++J)
        Builders.emplace_back(buildProofs);
      for (std::thread &Builder : Builders)
        Builder.join();
    }
    std::map<std::string, std::string> Failures;
    std::string Built;
    for (size_t I = 0; I != Proofs.size(); ++I) {
      if (BuildErrors[I]) {
        Failures[Proofs[I].Name] = *BuildErrors[I];
        continue;
      }
      Built += Proofs[I].Entry;
    }
    if (Built.empty())
      return Failures;

    const std::string Certifier =
        leanProjectPath(Root, {".cppverify", "Certify.lean"});
    const std::string GoalList = leanProjectPath(Root, {".cppverify", "goals"});
    if (std::error_code EC = llvm::sys::fs::create_directories(
            llvm::sys::path::parent_path(Certifier)))
      return llvm::createStringError(EC, "cannot create %s", Certifier.c_str());
    if (llvm::Error Error = writeTextFile(Certifier, LeanCertifierSource))
      return std::move(Error);
    if (llvm::Error Error = writeTextFile(GoalList, Built))
      return std::move(Error);
    auto Checked = runLake({"env", "lean", "--run", Certifier, GoalList,
                            "propext,Quot.sound,Classical.choice"},
                           "certify");
    if (!Checked)
      return Checked.takeError();
    std::set<std::string> Checks;
    for (llvm::StringRef Rest = *Checked; !Rest.empty();) {
      auto [Line, Next] = Rest.split('\n');
      Rest = Next;
      llvm::SmallVector<llvm::StringRef, 3> Fields;
      Line.split(Fields, '\t', 2);
      if (Fields.size() < 2 || (Fields[0] != "ok" && Fields[0] != "fail"))
        continue;
      Checks.insert(Fields[1].str());
      if (Fields[0] == "fail")
        Failures[Fields[1].str()] =
            Fields.size() == 3 ? Fields[2].str() : "the certifier failed";
    }
    for (const Build &Proof : Proofs)
      if (!Failures.count(Proof.Name) && !Checks.count(Proof.Name))
        Failures[Proof.Name] = "the certifier did not check it";
    return Failures;
  }

  // What cppverify_auto made of a goal: the step that proves it, or why it
  // did not.
  struct LeanTrial {
    std::string Step;
    std::string Why;
  };

  // Runs cppverify_auto on each goal in one Lean process, in order, and keeps
  // a proof only when the kernel accepted it with Lean's foundational axioms
  // alone: a probe of the suite saw a step claim a false goal with a term the
  // kernel rejected. Lean reports to a file, line by line (its messages come
  // from a thread of its own, buffered, and are lost when it is stopped): the
  // step that proved each goal, then the axioms of its theorem, or that the
  // kernel rejected it. A goal with an error is elaborated with sorryAx. A
  // goal that takes longer than Limit, or stops Lean, is not proved, and the
  // goals after it start again in a new process; heartbeats bound no kernel
  // check. Goals Lean cannot start on are left out.
  std::map<std::string, LeanTrial>
  tryLeanGoals(const std::vector<const LeanProjectGoal *> &Goals,
               const std::string &Lean,
               const std::vector<std::string> &Environment, unsigned Chunk,
               std::optional<std::chrono::milliseconds> Limit,
               std::string &Failure) {
    std::map<std::string, LeanTrial> Trials;
    const std::string Dir =
        leanProjectPath(leanProjectRoot(), {".cppverify", "automation"});
    if (std::error_code EC = llvm::sys::fs::create_directories(Dir)) {
      Failure = "cannot create " + Dir + ": " + EC.message();
      return Trials;
    }
    const std::string Base =
        leanProjectPath(Dir, {"try-" + std::to_string(Chunk)});
    const std::string Source = Base + ".lean", Report = Base + ".report",
                      Log = Base + ".log";
    auto leanString = [](llvm::StringRef Text) {
      std::string Quoted = "\"";
      for (char C : Text) {
        if (C == '\\' || C == '"')
          Quoted += '\\';
        Quoted += C;
      }
      return Quoted + "\"";
    };
    const std::string ReportName = leanString(Report);
    static const llvm::StringRef Foundations[] = {"propext", "Quot.sound",
                                                  "Classical.choice"};
    const std::string Limited =
        Limit
            ? " within " + std::to_string((Limit->count() + 999) / 1000) + " s"
            : "";

    for (size_t Next = 0; Next < Goals.size() && !interruptRequested();) {
      std::string Text = "import CppVerify.Generated\nimport CppVerify.User\n"
                         "import CppVerify.Auto\n\n"
                         "set_option cppverify.autoReport " +
                         ReportName + "\n#eval CppVerify.Auto.report " +
                         ReportName + " \"ready\"\n";
      for (size_t I = Next; I != Goals.size(); ++I) {
        const LeanProjectGoal &Goal = *Goals[I];
        const std::string Name = "cppverify_try_" + std::to_string(I);
        Text += "\ntheorem " + Name + " : " + Goal.Name + " := by\n  apply " +
                Goal.Name + ".of_readable\n";
        if (!Goal.Intros.empty())
          Text += "  intro " + Goal.Intros + "\n";
        Text += "  cppverify_auto\n#cppverify_axioms " + ReportName + " " +
                Name + "\n";
      }
      llvm::sys::fs::remove(Report);
      if (llvm::Error Error = writeTextFile(Source, Text)) {
        Failure = llvm::toString(std::move(Error));
        return Trials;
      }

      std::vector<llvm::StringRef> Args = {Lean, "-DmaxErrors=1000000",
                                           "-DElab.async=false", Source};
      std::vector<llvm::StringRef> Env(Environment.begin(), Environment.end());
      std::optional<llvm::StringRef> Redirects[] = {
          llvm::StringRef(""), llvm::StringRef(Log), llvm::StringRef(Log)};
      std::string StartError;
      bool StartFailed = false;
      llvm::sys::ProcessInfo Process = llvm::sys::ExecuteNoWait(
          Lean, Args, Env, Redirects, 0, &StartError, &StartFailed);
      if (StartFailed || Process.Pid == llvm::sys::ProcessInfo::InvalidPid) {
        Failure = "cannot start Lean: " + StartError;
        return Trials;
      }

      bool Started = false;
      std::map<size_t, std::string> Steps, Axioms;
      size_t Parsed = 0;
      auto readReport = [&] {
        auto Buffer = llvm::MemoryBuffer::getFile(Report, /*IsText=*/false,
                                                  /*RequiresNullTerminator=*/
                                                  false);
        if (!Buffer)
          return;
        llvm::StringRef All = (*Buffer)->getBuffer();
        while (Parsed < All.size()) {
          const size_t End = All.find('\n', Parsed);
          if (End == llvm::StringRef::npos)
            break;
          llvm::StringRef Line = All.slice(Parsed, End).rtrim('\r');
          Parsed = End + 1;
          if (Line == "ready") {
            Started = true;
            continue;
          }
          llvm::SmallVector<llvm::StringRef, 3> Fields;
          Line.split(Fields, '\t', 2);
          size_t I;
          if (Fields.size() != 3 ||
              !Fields[1].consume_front("cppverify_try_") ||
              Fields[1].getAsInteger(10, I))
            continue;
          (Fields[0] == "step" ? Steps : Axioms)[I] = Fields[2].str();
        }
      };

      auto Progress = std::chrono::steady_clock::now();
      size_t Finished = 0;
      std::optional<std::string> Stopped;
      bool TimedOut = false;
      while (true) {
        ChildPoll Poll = pollChild(Process, "Lean");
        readReport();
        if (Axioms.size() != Finished) {
          Finished = Axioms.size();
          Progress = std::chrono::steady_clock::now();
        }
        if (Poll.State != ChildState::Running) {
          if (Poll.State == ChildState::Failed || Poll.ExitCode < 0)
            Stopped = Poll.Error;
          break;
        }
        std::string KillError;
        if (interruptRequested()) {
          terminateChild(Process, "Lean", KillError);
          return Trials;
        }
        const auto Elapsed = std::chrono::steady_clock::now() - Progress;
        if (!Started && Elapsed > std::chrono::minutes(2)) {
          terminateChild(Process, "Lean", KillError);
          Failure = "Lean did not load the project's modules within 2 minutes";
          return Trials;
        }
        if (Started && Limit && Elapsed > *Limit) {
          terminateChild(Process, "Lean", KillError);
          TimedOut = true;
          break;
        }
        std::this_thread::sleep_for(std::chrono::milliseconds(20));
      }
      if (!Started) {
        auto Output = llvm::MemoryBuffer::getFile(Log);
        Failure =
            "Lean could not start on the goals" +
            (Output && !(*Output)->getBuffer().trim().empty()
                 ? ": " + (*Output)->getBuffer().trim().take_front(300).str()
                 : std::string());
        return Trials;
      }

      size_t I = Next;
      for (; I != Goals.size() && Axioms.count(I); ++I) {
        LeanTrial &Trial = Trials[Goals[I]->Name];
        llvm::SmallVector<llvm::StringRef, 4> Used;
        llvm::StringRef(Axioms[I]).split(Used, ',', -1, false);
        const bool Foundational =
            Axioms[I] != "missing" &&
            llvm::all_of(Used, [&](llvm::StringRef Axiom) {
              return llvm::is_contained(Foundations, Axiom.trim());
            });
        auto Step = Steps.find(I);
        if (Foundational && Step != Steps.end() &&
            llvm::is_contained(LeanAutomationSteps, Step->second))
          Trial.Step = Step->second;
        else
          Trial.Why = "did not prove it";
      }
      if (I == Goals.size())
        break;
      // The goal Lean was on when it stopped, or ran out of time.
      Trials[Goals[I]->Name].Why =
          TimedOut ? "did not prove it" + Limited
                   : "did not prove it: Lean stopped" +
                         (Stopped && !Stopped->empty() ? " (" + *Stopped + ")"
                                                       : std::string());
      Next = I + 1;
    }
    return Trials;
  }

  // The goals cppverify_auto proves, from the proof files as they are now.
  std::set<std::string>
  automaticLeanGoals(const std::vector<LeanProjectGoal> &ProjectGoals) const {
    std::set<std::string> Automatic;
    for (const LeanProjectGoal &Goal : ProjectGoals) {
      std::string File;
      if (!Goal.Exported || Automatic.count(Goal.Name))
        continue;
      if (std::optional<LeanProofRecord> Record = readLeanProof(leanProjectPath(
              leanProjectRoot(), leanProofComponents(Goal, File))))
        if (Record->Automatic)
          Automatic.insert(Goal.Name);
    }
    return Automatic;
  }

  // Tries cppverify_auto on each goal whose proof file is still the one
  // cpp-verify wrote and that this revision has not tried, as Vermilion and
  // Why3 run their automation when they generate goals, and writes what it
  // finds: the step that proves the goal, or a stub that says it was tried.
  // It runs the pinned toolchain; without it the stubs stay as they are.
  void automateLeanProject(const std::vector<LeanProjectGoal> &ProjectGoals) {
    const std::string &Root = leanProjectRoot();
    std::map<std::string, const LeanProjectGoal *> Unique;
    for (const LeanProjectGoal &Goal : ProjectGoals)
      if (Goal.Exported)
        Unique.emplace(Goal.Name, &Goal);
    auto pathOf = [&](const LeanProjectGoal &Goal) {
      std::string File;
      return leanProjectPath(Root, leanProofComponents(Goal, File));
    };
    std::vector<const LeanProjectGoal *> Candidates;
    for (const auto &[Name, Goal] : Unique)
      if (std::optional<LeanProofRecord> Record = readLeanProof(pathOf(*Goal)))
        if (Record->Pristine && !llvm::StringRef(Record->Automation)
                                     .starts_with(leanAutomationTag()))
          Candidates.push_back(Goal);
    if (Candidates.empty() || interruptRequested())
      return;

    auto Launcher = leanLauncher(".cppverify-automation");
    if (!Launcher) {
      llvm::consumeError(Launcher.takeError());
      return;
    }
    auto skipped = [&](const std::string &Why) {
      Warnings.push_back(
          "cppverify_auto was not tried on the new Lean goals: " + Why);
    };
    if (auto Build = Launcher->run({"build", "CppVerify.Generated",
                                    "CppVerify.User", "CppVerify.Auto"},
                                   "build", Root);
        !Build)
      return skipped(
          "the project does not build (" +
          llvm::StringRef(llvm::toString(Build.takeError())).rtrim().str() +
          ")");
    auto Variables = Launcher->run({"env"}, "env", Root);
    if (!Variables)
      return skipped(llvm::toString(Variables.takeError()));
    std::string Lean, LeanPath;
    for (llvm::StringRef Rest = *Variables; !Rest.empty();) {
      auto [Line, Next] = Rest.split('\n');
      Rest = Next;
      Line = Line.rtrim("\r");
      if (Line.consume_front("LEAN="))
        Lean = Line.str();
      else if (Line.consume_front("LEAN_PATH="))
        LeanPath = Line.str();
    }
    if (Lean.empty() || LeanPath.empty())
      return skipped("lake env names no Lean or LEAN_PATH");
    const std::vector<std::string> Environment =
        childEnvironment("LEAN_PATH", LeanPath);

    const unsigned Jobs = leanJobs(Candidates.size());
    std::vector<std::vector<const LeanProjectGoal *>> Chunks(Jobs);
    for (size_t I = 0; I != Candidates.size(); ++I)
      Chunks[I % Jobs].push_back(Candidates[I]);
    std::optional<std::chrono::milliseconds> Limit;
    if (Opts.LeanAutoTimeoutMs)
      Limit = std::chrono::milliseconds(Opts.LeanAutoTimeoutMs);
    std::vector<std::map<std::string, LeanTrial>> Results(Jobs);
    std::vector<std::string> Failures(Jobs);
    {
      std::vector<std::thread> Threads;
      for (unsigned C = 0; C != Jobs; ++C)
        Threads.emplace_back([&, C] {
          Results[C] =
              tryLeanGoals(Chunks[C], Lean, Environment, C, Limit, Failures[C]);
        });
      for (std::thread &Thread : Threads)
        Thread.join();
    }

    const std::string Tag = leanAutomationTag();
    for (const std::map<std::string, LeanTrial> &Result : Results)
      for (const auto &[Name, Trial] : Result) {
        const LeanProjectGoal &Goal = *Unique.at(Name);
        const std::string Text =
            Trial.Step.empty()
                ? leanProofHeader(Goal, Tag + Trial.Why) +
                      leanProof(Goal.Name, Goal.Group, Goal.Intros, "sorry")
                : leanProofHeader(Goal, Tag + "proves it with " + Trial.Step,
                                  /*Automatic=*/true) +
                      leanProof(Goal.Name, Goal.Group, Goal.Intros, Trial.Step);
        if (llvm::Error Error = writeTextFile(pathOf(Goal), Text))
          Failures.push_back(llvm::toString(std::move(Error)));
      }
    std::set<std::string> Reported;
    for (const std::string &Failure : Failures)
      if (!Failure.empty() && Reported.insert(Failure).second)
        Warnings.push_back("cppverify_auto stopped before every new Lean goal "
                           "was tried: " +
                           Failure);
  }
};

class Verifier {
  ASTContext &Ctx;
  VerifyOptions Opts;
  llvm::raw_ostream *DumpOS = nullptr;
  std::vector<VerifyDiagnostic> Diags;
  /// What --list-functions prints: each function's location and kind.
  std::vector<std::pair<SourceLocation, std::string>> Listing;
  std::optional<LeanProject> Lean;
  /// Where each template specialization verified is instantiated, and what
  /// it is, by its function's name.
  std::map<std::string, std::pair<SourceLocation, std::string>>
      InstantiationPoints;

  /// The instantiation a diagnostic about a template specialization is
  /// about, which a compiler notes after an error or a warning.
  const std::pair<SourceLocation, std::string> *
  instantiationOf(const VerifyDiagnostic &D) const {
    if ((D.K != VerifyDiagnostic::Error && D.K != VerifyDiagnostic::Warning) ||
        (D.Loc.isInvalid() && D.Span.isInvalid()))
      return nullptr;
    auto It = InstantiationPoints.find(D.FunctionName);
    if (It == InstantiationPoints.end() || It->second.first.isInvalid())
      return nullptr;
    return &It->second;
  }

  void reportLeanWarnings() {
    for (std::string &Warning : Lean->takeWarnings())
      Diags.push_back({VerifyDiagnostic::Warning, std::move(Warning)});
  }

  /// The archive record of Module, empty without --obligation-out.
  llvm::Expected<std::string> archiveRecord(const ObligationModule &Module) {
    if (!Opts.ObligationOut)
      return std::string();
    // A record states each term in full, a subterm that goals share at each
    // of its places.
    if (Opts.MaxQueryNodes != 0 &&
        obligationModuleTreeNodesUpTo(Module, Opts.MaxQueryNodes) >
            Opts.MaxQueryNodes)
      return llvm::createStringError(
          llvm::inconvertibleErrorCode(),
          "its record would state more than %llu expression nodes, the limit "
          "(--max-query-nodes)",
          static_cast<unsigned long long>(Opts.MaxQueryNodes));

    std::string Serialized = serializeObligationModule(Module);
    auto RoundTrip = deserializeObligationModules(Serialized);
    if (!RoundTrip)
      return RoundTrip.takeError();
    if (RoundTrip->size() != 1 ||
        serializeObligationModule(RoundTrip->front()) != Serialized ||
        obligationSemanticHash(RoundTrip->front()) !=
            obligationSemanticHash(Module))
      return llvm::createStringError(
          llvm::inconvertibleErrorCode(),
          "canonical obligation serialization did not round-trip");
    return Serialized;
  }

  llvm::Error emitObligationArchive(const ObligationModule &Module) {
    llvm::Expected<std::string> Record = archiveRecord(Module);
    if (!Record)
      return Record.takeError();
    if (Opts.ObligationOut)
      *Opts.ObligationOut << *Record;
    return llvm::Error::success();
  }

  void annotateObligationSources(ObligationModule &Module) {
    const SourceManager &SourceMgr = Ctx.getSourceManager();
    auto annotateSource = [&](SourceLocation Loc, SourceLocation EndLoc,
                              ObligationSource &Source) {
      if (!Loc.isValid())
        return;
      PresumedLoc Location = SourceMgr.getPresumedLoc(Loc);
      if (!Location.isValid())
        return;
      ObligationSource Found;
      Found.File = Location.getFilename();
      Found.Line = Location.getLine();
      Found.Column = Location.getColumn();
      PresumedLoc End =
          SourceMgr.getPresumedLoc(EndLoc.isValid() ? EndLoc : Loc);
      if (End.isValid() && Found.File == End.getFilename() &&
          (End.getLine() > Found.Line ||
           (End.getLine() == Found.Line && End.getColumn() >= Found.Column))) {
        Found.EndLine = End.getLine();
        Found.EndColumn = End.getColumn();
      } else {
        Found.EndLine = Found.Line;
        Found.EndColumn = Found.Column;
      }
      // A term shared with a module annotated before, which other threads
      // may be reading, is read and not written.
      if (Source.File != Found.File || Source.Line != Found.Line ||
          Source.Column != Found.Column || Source.EndLine != Found.EndLine ||
          Source.EndColumn != Found.EndColumn)
        Source = std::move(Found);
    };
    // Terms share subterms: each node once.
    llvm::DenseSet<const LogicExpr *> Annotated;
    auto annotateExpr = [&](const LogicExpr *Root) {
      if (!Root)
        return;
      std::vector<const LogicExpr *> Pending = {Root};
      while (!Pending.empty()) {
        const LogicExpr *Expr = Pending.back();
        Pending.pop_back();
        if (!Annotated.insert(Expr).second)
          continue;
        annotateSource(Expr->Loc, Expr->EndLoc, Expr->Source);
        for (const auto &Child : Expr->Children)
          if (Child)
            Pending.push_back(Child.get());
      }
    };

    annotateExpr(Module.CorrectnessGoal.get());
    annotateExpr(Module.CounterexampleQuery.get());
    std::map<std::string, unsigned> StableIdCounts;
    for (Obligation &Item : Module.Obligations) {
      annotateSource(Item.Loc, Item.EndLoc, Item.Source);
      std::string StableId =
          Module.FunctionIdentity + "::" + obligationKindName(Item.Kind) + "@";
      StableId += Item.Source.isValid()
                      ? std::to_string(Item.Source.Line) + ":" +
                            std::to_string(Item.Source.Column)
                      : "synthetic";
      unsigned &Count = StableIdCounts[StableId];
      if (++Count > 1)
        StableId += "#" + std::to_string(Count);
      Item.StableId = std::move(StableId);
      annotateExpr(Item.Goal.get());
      annotateExpr(Item.CounterexampleQuery.get());
    }
    for (auto &[InternalName, Variable] : Module.DiagnosticVariables) {
      (void)InternalName;
      annotateSource(Variable.Loc, Variable.EndLoc, Variable.Source);
    }
    for (DiagnosticTraceEvent &Event : Module.TraceEvents) {
      annotateSource(Event.Loc, Event.EndLoc, Event.Source);
      annotateExpr(Event.Guard.get());
      for (DiagnosticTraceValue &Value : Event.Values)
        annotateExpr(Value.Value.get());
    }
    for (auto &[Identity, Function] : Module.LogicFunctions) {
      (void)Identity;
      annotateExpr(Function.StepDefinition.get());
      for (auto &Definition : Function.DefinitionLevels)
        annotateExpr(Definition.get());
    }
  }

  void checkCalleeRecommendsOnFailure(const VFunction &Caller,
                                      const FunctionMap &FnMap,
                                      VerifyBackend &Backend) {
    NodeBudget::Limit NodeLimit(Opts.MaxQueryNodes);
    std::vector<const VSpecCallExpr *> Calls;
    collectSpecCallsInFunction(Caller, Calls);
    for (const VSpecCallExpr *C : Calls) {
      auto It = FnMap.find(C->CalleeIdentity);
      if (It == FnMap.end() || It->second->Recommends.empty())
        continue;
      std::map<std::string, std::unique_ptr<VExpr>> ArgMap;
      for (unsigned I = 0; I < It->second->Params.size() && I < C->Args.size();
           ++I)
        ArgMap[It->second->Params[I].first] = cloneVExpr(C->Args[I].get());
      PassiveProgram PP;
      PP.FunctionName = Caller.Name + ".recommends";
      PP.FunctionIdentity =
          Caller.Identity + "::recommends::" + C->CalleeIdentity;
      for (const auto &Pre : Caller.Preconditions)
        PP.EntryAssumes.push_back(cloneVExpr(Pre.get()));
      for (const auto &Rec : It->second->Recommends) {
        auto Inst = substParamsInExpr(Rec.get(), ArgMap);
        if (!Inst)
          continue;
        Inst = SpecInliner(FnMap, Caller.SpecFuel).inlineExpr(std::move(Inst));
        PP.ExitAsserts.push_back(
            {ProofObligationKind::Recommends, std::move(Inst)});
      }
      if (PP.ExitAsserts.empty())
        continue;
      PP.CallerIntMode = Caller.IntMode;
      auto Module = buildObligationModule(PP, Opts.MaxQueryNodes);
      if (!Module) {
        Diags.push_back({VerifyDiagnostic::Unresolved,
                         "recommends lowering failed for " + Caller.Name +
                             " (" + llvm::toString(Module.takeError()) + ")"});
        continue;
      }
      annotateObligationSources(*Module);
      VerifyResult R = Backend.verify(*Module);
      if (R.Status == VerifyStatus::Failed)
        Diags.push_back({VerifyDiagnostic::Warning,
                         "recommends of spec " + C->Callee +
                             " may be violated at call in " + Caller.Name});
    }
  }

public:
  Verifier(ASTContext &Ctx, const VerifyOptions &Opts,
           llvm::raw_ostream &DumpOS)
      : Ctx(Ctx), Opts(Opts), DumpOS(&DumpOS) {}

  bool run() {
    if (!Opts.LeanOutPath.empty() && Opts.Backend != BackendKind::Lean) {
      Diags.push_back(
          {VerifyDiagnostic::Error, "--lean-out requires --backend=lean"});
      return false;
    }
    if (!Opts.LeanProjectPath.empty() && Opts.Backend != BackendKind::Lean) {
      Diags.push_back(
          {VerifyDiagnostic::Error, "--lean-project requires --backend=lean"});
      return false;
    }
    if (!Opts.LeanFallbackProjectPath.empty() &&
        Opts.Backend != BackendKind::Z3 &&
        Opts.Backend != BackendKind::Portfolio &&
        Opts.Backend != BackendKind::Race) {
      Diags.push_back({VerifyDiagnostic::Error,
                       "--lean-fallback requires --backend=z3, "
                       "--backend=portfolio, or --backend=race"});
      return false;
    }
    if (!Opts.LeanFallbackProjectPath.empty() &&
        (!Opts.LeanProjectPath.empty() || !Opts.LeanOutPath.empty())) {
      Diags.push_back(
          {VerifyDiagnostic::Error,
           "--lean-fallback is mutually exclusive with --lean-project and "
           "--lean-out"});
      return false;
    }
    if (!Opts.LeanFallbackProjectPath.empty() && Opts.LowerOnly) {
      Diags.push_back({VerifyDiagnostic::Error,
                       "--lean-fallback cannot be combined with --lower-only"});
      return false;
    }
    if (!Opts.LeanProjectPath.empty() && !Opts.LeanOutPath.empty()) {
      Diags.push_back({VerifyDiagnostic::Error,
                       "--lean-project and --lean-out are mutually exclusive"});
      return false;
    }
    if (Opts.LeanCertify && Opts.LeanProjectPath.empty() &&
        Opts.LeanFallbackProjectPath.empty()) {
      Diags.push_back({VerifyDiagnostic::Error,
                       "--lean-certify requires --lean-project or "
                       "--lean-fallback"});
      return false;
    }
    if (Opts.LeanPruneStale && Opts.LeanProjectPath.empty() &&
        Opts.LeanFallbackProjectPath.empty()) {
      Diags.push_back({VerifyDiagnostic::Error,
                       "--lean-prune-stale requires --lean-project or "
                       "--lean-fallback"});
      return false;
    }
    if (!Opts.LeanAuto && Opts.LeanProjectPath.empty() &&
        Opts.LeanFallbackProjectPath.empty()) {
      Diags.push_back({VerifyDiagnostic::Error,
                       "--no-lean-auto requires --lean-project or "
                       "--lean-fallback"});
      return false;
    }
    if (Opts.LowerOnly && Opts.Backend == BackendKind::Lean) {
      Diags.push_back(
          {VerifyDiagnostic::Error,
           "--lower-only supports Z3, cvc5, portfolio, and BMC; use "
           "--backend=lean to validate Lean export"});
      return false;
    }
    if (Opts.Backend == BackendKind::Lean && !Opts.ProofCachePath.empty()) {
      Diags.push_back({VerifyDiagnostic::Error,
                       "--proof-cache is not supported by the Lean backend"});
      return false;
    }
    if (Opts.Backend == BackendKind::Lean && Opts.Jobs != 1) {
      Diags.push_back({VerifyDiagnostic::Error,
                       "the Lean backend exports one function at a time; "
                       "LeanJobs sets its Lean processes"});
      return false;
    }
    if (Opts.Backend == BackendKind::CVC5 && !Opts.ProofCachePath.empty()) {
      Diags.push_back({VerifyDiagnostic::Error,
                       "--proof-cache is not supported by --backend=cvc5; use "
                       "--backend=portfolio to cache its Z3 component"});
      return false;
    }
    if (!Opts.CVC5Path.empty() && Opts.Backend != BackendKind::CVC5 &&
        Opts.Backend != BackendKind::Portfolio &&
        Opts.Backend != BackendKind::Race) {
      Diags.push_back({VerifyDiagnostic::Error,
                       "--cvc5-path requires --backend=cvc5, "
                       "--backend=portfolio, or --backend=race"});
      return false;
    }
    if (Opts.LowerOnly && !Opts.ProofCachePath.empty()) {
      Diags.push_back({VerifyDiagnostic::Error,
                       "--proof-cache cannot be combined with --lower-only"});
      return false;
    }
    // Pruning may remove an entry that another function still looks up, so
    // the run prunes once, after everything that may look one up.
    llvm::scope_exit PruneProofCache([&] {
      if (llvm::Error Error =
              pruneProofCache(Opts.ProofCachePath, Opts.ProofCacheMaxBytes,
                              Opts.ProofCacheMaxEntries))
        Diags.push_back({VerifyDiagnostic::Warning,
                         "cannot prune the proof cache: " +
                             llvm::toString(std::move(Error))});
    });

    ASTConverter DiscoveryConverter(Ctx);
    auto DiscoveryFunctions = DiscoveryConverter.convertTranslationUnit();
    inferFreshOwnedReturns(DiscoveryFunctions);
    std::set<std::string> FreshOwnedCalleeIdentities;
    for (const auto &Fn : DiscoveryFunctions)
      if (Fn->FreshOwnedReturn)
        FreshOwnedCalleeIdentities.insert(Fn->Identity);

    ASTConverter Converter(Ctx, FreshOwnedCalleeIdentities);
    auto Functions = Converter.convertTranslationUnit();
    const std::map<std::string, std::set<std::string>> UnverifiedCallers =
        Converter.getUnverifiedCallers();
    for (const auto &[Loc, Message] : Converter.getWarnings())
      Diags.push_back({VerifyDiagnostic::Warning, Message, Loc});
    InstantiationPoints = Converter.getInstantiationPoints();
    // A construct the verifier does not represent costs its function alone:
    // the function is Unresolved, its first error carrying the verdict, and
    // the rest of the translation unit is verified. An error outside every
    // function stops the run.
    // --function: the functions the run reports, by their names.
    std::vector<llvm::GlobPattern> Patterns;
    for (const std::string &Text : Opts.FunctionPatterns) {
      auto Pattern = llvm::GlobPattern::create(Text);
      if (!Pattern) {
        Diags.push_back(
            {VerifyDiagnostic::Error, "--function=" + Text + ": " +
                                          llvm::toString(Pattern.takeError())});
        return false;
      }
      Patterns.push_back(std::move(*Pattern));
    }
    auto selects = [&](llvm::StringRef Name) {
      return Patterns.empty() ||
             llvm::any_of(Patterns, [&](const llvm::GlobPattern &Pattern) {
               return Pattern.match(Name);
             });
    };
    bool OutsideFunctions = false;
    std::map<std::string, std::string> UnsupportedConstructs;
    for (const ConversionError &Err : Converter.getErrors()) {
      VerifyDiagnostic D{VerifyDiagnostic::Error, Err.Message,
                         Err.Range.getBegin()};
      D.Span = Err.Range;
      if (Err.Function.empty())
        OutsideFunctions = true;
      else
        D.FunctionName = Err.FunctionName;
      D.Hidden = !Err.Function.empty() && !selects(Err.FunctionName);
      if (!Err.Function.empty() &&
          UnsupportedConstructs.emplace(Err.Function, Err.Message).second) {
        VerifyResult R;
        R.Status = VerifyStatus::Unresolved;
        R.Reason = VerifyReason::UnsupportedConstruct;
        R.Message = Err.Message;
        D.Result = std::move(R);
      }
      Diags.push_back(std::move(D));
    }
    if (OutsideFunctions)
      return false;
    if (Functions.empty() && !UnsupportedConstructs.empty())
      return false;
    if (Functions.empty()) {
      if (Opts.LeanCertify) {
        Diags.push_back({VerifyDiagnostic::Unresolved,
                         "Lean certification requires at least one proof "
                         "obligation"});
        return false;
      }
      Diags.push_back(
          {VerifyDiagnostic::Warning, "no verifiable functions found"});
      return true;
    }
    // A function is selected by the name its verdicts print, which for an
    // inductive predicate's step is the predicate's; the predicate's rule
    // proofs are reported with it.
    std::vector<bool> Selected(Functions.size());
    for (size_t I = 0; I != Functions.size(); ++I) {
      const VFunction &Fn = *Functions[I];
      Selected[I] =
          selects(Fn.InductiveStepOf.empty() ? Fn.Name : Fn.InductiveStepOf);
    }
    std::set<std::string> SelectedIdentities;
    for (size_t I = 0; I != Functions.size(); ++I)
      if (Selected[I])
        SelectedIdentities.insert(Functions[I]->Identity);
    for (size_t I = 0; I != Functions.size(); ++I)
      Selected[I] = Selected[I] ||
                    SelectedIdentities.count(Functions[I]->InductiveRuleOf);
    if (!Patterns.empty() &&
        llvm::none_of(Selected, [](bool S) { return S; }) &&
        llvm::none_of(Converter.getErrors(), [&](const ConversionError &Err) {
          return !Err.Function.empty() && selects(Err.FunctionName);
        })) {
      Diags.push_back({VerifyDiagnostic::Error,
                       "no function matches --function=" +
                           llvm::join(Opts.FunctionPatterns, ", --function=")});
      return false;
    }
    if (Opts.ListFunctions) {
      for (size_t I = 0; I != Functions.size(); ++I) {
        const auto &Fn = Functions[I];
        if (Fn->IsBuiltin || Fn->IsChoice || !Fn->InductiveStepOf.empty() ||
            !Fn->InductiveRuleOf.empty() || !Selected[I])
          continue;
        const char *Kind = Fn->IsConstexprSpec ? "constexpr spec"
                           : Fn->IsSpec        ? "spec"
                           : Fn->IsProof       ? "proof"
                           : Fn->IsTrusted     ? "trusted"
                                               : "function";
        Listing.push_back({Fn->DeclLoc, std::string(Kind) + " " + Fn->Name});
      }
      return true;
    }
    inferFreshOwnedReturns(Functions);
    inferOutParameters(Functions);

    FunctionMap FnMap;
    for (const auto &Fn : Functions)
      FnMap[Fn->Identity] = Fn.get();

    std::vector<std::unique_ptr<VFunction>> InterfaceFunctions;
    FunctionMap InterfaceMap;
    // A contract whose extent markers cannot be read, by function identity.
    std::map<std::string, std::string> InterfaceErrors;
    InterfaceFunctions.reserve(Functions.size());
    for (const auto &Fn : Functions) {
      auto Interface = std::make_unique<VFunction>(cloneVFunction(*Fn));
      if (!Interface->IsSpec && Opts.CheckUB &&
          (isDeductiveBackend(Opts.Backend) ||
           Opts.Backend == BackendKind::BMC ||
           Opts.Backend == BackendKind::Lean))
        if (auto Error = instrumentUBChecks(*Interface))
          InterfaceErrors[Interface->Identity] = *Error;
      InterfaceMap[Interface->Identity] = Interface.get();
      InterfaceFunctions.push_back(std::move(Interface));
    }

    std::vector<LeanProjectGoal> LeanProjectGoals;
    // The goal groups of the modules a fallback run gave its solver, which
    // it examines in Lean only when the solver leaves them unresolved.
    std::set<std::string> LeanRunGroups;
    std::unique_ptr<llvm::raw_fd_ostream> LeanFile;
    llvm::raw_ostream *LeanOut = DumpOS;
    std::string LeanOutputPath = Opts.LeanOutPath;
    const bool HasLeanProject =
        !Opts.LeanProjectPath.empty() || !Opts.LeanFallbackProjectPath.empty();
    // A project's goals go to modules, one per function.
    LeanProjectModules LeanModules;
    if (HasLeanProject) {
      Lean.emplace(Opts);
      llvm::Error Error = Lean->initializeLeanProject();
      reportLeanWarnings();
      if (Error) {
        Diags.push_back({VerifyDiagnostic::Error,
                         "cannot initialize Lean project (" +
                             llvm::toString(std::move(Error)) + ")"});
        return false;
      }
    } else if (Opts.Backend == BackendKind::Lean && !LeanOutputPath.empty()) {
      std::error_code EC;
      LeanFile = std::make_unique<llvm::raw_fd_ostream>(LeanOutputPath, EC,
                                                        llvm::sys::fs::OF_Text);
      if (EC) {
        Diags.push_back({VerifyDiagnostic::Error,
                         "cannot open lean output: " + LeanOutputPath});
        return false;
      }
      LeanOut = LeanFile.get();
    }

    // Z3 runs in this process, so its limit covers all its queries.
    setZ3MemoryLimit(Opts.MemoryLimitMB);
    BackendExecutionOptions Execution;
    Execution.SolverTimeoutMs = Opts.SolverTimeoutMs;
    Execution.CollectionTimeoutMs = Opts.CollectionTimeoutMs;
    Execution.CertifyTimeoutMs = Opts.CertifyTimeoutMs;
    Execution.SolverResourceLimit = Opts.SolverResourceLimit;
    Execution.MaxQueryNodes = Opts.MaxQueryNodes;
    Execution.MemoryLimitMB = Opts.MemoryLimitMB;
    Execution.IntegerEncoding = Opts.IntegerEncoding;
    Execution.SkipWholeModuleRetry = !Opts.LeanFallbackProjectPath.empty();
    Execution.MaxFailures = Opts.MaxFailures;
    Execution.CVC5Path = Opts.CVC5Path;
    Execution.ProfileQuantifiers = Opts.ProfileQuantifiers;
    Execution.ProofCachePath = Opts.ProofCachePath;
    Execution.ProofCacheMaxBytes = Opts.ProofCacheMaxBytes;
    Execution.ProofCacheMaxEntries = Opts.ProofCacheMaxEntries;
    // Functions are verified as tasks. With more than one job they run at
    // once on one pool of exactly that many workers, which the backends also
    // use for their obligations; each task has its own backends and buffers,
    // and the results are merged in source order. Lean exports stay serial.
    const unsigned Workers = llvm::heavyweight_hardware_concurrency(Opts.Jobs)
                                 .compute_thread_count();
    const bool Parallel = Workers > 1 && Opts.Backend != BackendKind::Lean &&
                          Opts.LeanFallbackProjectPath.empty() &&
                          !Opts.LeanCertify;
    Execution.Jobs = Workers;
    std::optional<llvm::StdThreadPool> Pool;
    if (Parallel) {
      Pool.emplace(llvm::heavyweight_hardware_concurrency(Workers));
      Execution.Pool = &*Pool;
    }
    std::unique_ptr<VerifyBackend> SharedBackend;
    if (!Parallel)
      SharedBackend = createVerifyBackend(
          Opts.Backend, LeanOut, Opts.BMCUnroll, Execution,
          Opts.LeanProjectPath.empty() ? nullptr : &LeanProjectGoals,
          Opts.LeanProjectPath.empty() ? nullptr : &LeanModules);
    std::unique_ptr<LeanVerifyBackend> LeanFallbackBackend;
    if (!Opts.LeanFallbackProjectPath.empty())
      LeanFallbackBackend =
          std::make_unique<LeanVerifyBackend>(&LeanModules, &LeanProjectGoals);
    // Vacuity checks: whether a verified function's end is reachable at all.
    // A vacuous path is refuted quickly; a satisfiable one is not worth
    // searching long, since an unsettled check only omits a warning.
    BackendExecutionOptions SmokeExecution = Execution;
    SmokeExecution.SolverTimeoutMs =
        Execution.SolverTimeoutMs == 0
            ? 1000
            : std::min<unsigned>(Execution.SolverTimeoutMs, 1000);
    SmokeExecution.CollectionTimeoutMs.reset();
    SmokeExecution.SingleQuery = true;
    SmokeExecution.Jobs = 1;
    SmokeExecution.Pool = nullptr;
    SmokeExecution.ProofCachePath.clear();
    auto falseGoal = [] {
      return std::make_unique<VLiteralExpr>(false, VType::makeBool(),
                                            SourceLocation());
    };
    const unsigned DumpLayers = Opts.DumpIRLayers;
    const bool MultiLayerDump = llvm::popcount(DumpLayers) > 1;
    bool AllOk = UnsupportedConstructs.empty();
    bool AnyFailed = false;
    std::set<std::string> FailedCallers;
    // A spec whose termination is not established has no definition, so a
    // proof that used it proves nothing.
    std::set<std::string> UndefinedSpecs;
    // Verdicts that assume callee contracts, and the callees they assume.
    std::vector<std::tuple<size_t, std::string, std::set<std::string>>>
        CallDependencies;
    // The verdict on each contract's definedness, by function identity.
    std::map<std::string, size_t> ContractChecks;
    // Frame facts of a spec whose reads clause is not established.
    std::set<std::string> UnframedSpecs;
    // Specs whose postcondition is not established.
    std::set<std::string> UnprovenPosts;
    // A verdict and the specs it relies on: their definitions and frames,
    // and their postconditions and unfoldings except where it withholds them.
    struct SpecReliance {
      size_t Index;
      std::set<std::string> Specs;
      std::set<std::string> Withheld;
      /// A check of a spec establishes these facts of it.
      std::string Establishes;
      unsigned Facts = 0;
      /// Specs whose postconditions, but not unfoldings, it does not assume.
      std::set<std::string> PostsWithheld;
      /// Proof functions whose contracts its proof blocks assume.
      std::set<std::string> Callees;
      /// The postconditions and unfoldings its module assumes.
      std::set<std::string> AssumedPosts;
      std::set<std::string> AssumedUnfoldings;
      /// The postconditions of its cluster that it assumes below its
      /// measure: they hold by the cluster's joint induction.
      std::set<std::string> InductivePosts;
    };
    enum : unsigned { DefinitionFact = 1, PostFact = 2, ReadsFact = 4 };
    std::vector<SpecReliance> ProofDependencies;
    // The line of each inductive predicate, which reports its rules.
    std::vector<std::pair<size_t, std::string>> InductiveLines;
    auto exportLeanFallbackTo = [&](std::vector<VerifyDiagnostic> &Out,
                                    const ObligationModule &Module,
                                    llvm::StringRef Label,
                                    const VerifyResult &SolverResult) {
      if (!LeanFallbackBackend)
        return false;
      const bool KnowsUnproved = SolverResult.UnprovedObligations &&
                                 !SolverResult.UnprovedObligations->empty();
      std::optional<std::set<std::string>> Selection;
      if (Opts.LeanScope == LeanFallbackScope::Unproved && KnowsUnproved)
        Selection.emplace(SolverResult.UnprovedObligations->begin(),
                          SolverResult.UnprovedObligations->end());
      ProofEvidence Evidence;
      Evidence.Solver = SolverResult.BackendName;
      Evidence.Total = Module.Obligations.size();
      if (KnowsUnproved)
        Evidence.SolverProved =
            Evidence.Total - SolverResult.UnprovedObligations->size();
      for (const Obligation &Item : Module.Obligations)
        if (!Selection || Selection->count(Item.Id))
          Evidence.LeanObligations.push_back(
              Item.StableId.empty() ? Item.Id : Item.StableId);
      LeanFallbackBackend->selectObligations(std::move(Selection));
      VerifyResult Fallback = LeanFallbackBackend->verify(Module);
      LeanFallbackBackend->selectObligations(std::nullopt);
      if (Fallback.Status == VerifyStatus::Exported) {
        std::string Message = "lean fallback: " + Label.str() +
                              evidenceSuffix(Evidence, "exported");
        Fallback.Evidence = std::move(Evidence);
        Out.push_back({VerifyDiagnostic::Exported, std::move(Message),
                       Fallback.Location, Label.str(), std::move(Fallback)});
        return true;
      }
      std::string Message = "lean fallback export failed: " + Label.str();
      if (!Fallback.Message.empty())
        Message += " (" + Fallback.Message + ")";
      Out.push_back({VerifyDiagnostic::Unresolved, std::move(Message),
                     Fallback.Location, Label.str(), std::move(Fallback)});
      return false;
    };

    struct FunctionRun {
      std::vector<VerifyDiagnostic> Diags;
      bool AllOk = true;
      bool AnyFailed = false;
      std::set<std::string> FailedCallers;
      std::set<std::string> UndefinedSpecs;
      std::vector<std::tuple<size_t, std::string, std::set<std::string>>>
          CallDependencies;
      std::set<std::string> UnframedSpecs;
      std::set<std::string> UnprovenPosts;
      std::vector<SpecReliance> ProofDependencies;
      std::vector<std::pair<size_t, std::string>> InductiveLines;
      /// Unresolved verdicts whose proposed counterexample its check could
      /// not evaluate, to be confirmed once it is known which contracts are
      /// established; Index is the verdict's place in Diags.
      struct Confirmation {
        size_t Index;
        std::shared_ptr<ObligationModule> Module;
        VerifyResult Result;
        const VFunction *Fn;
        std::string Label;
        BackendKind Kind;
      };
      std::vector<Confirmation> Confirmations;
      /// Certified failures a fallback project shows in Lean: each one's
      /// place in Diags and its refutation, or why it has none.
      struct Refutation {
        size_t Index;
        std::optional<LeanRefutation> Lean;
        std::string Why;
      };
      std::vector<Refutation> Refutations;
      /// For a verified proof function: what its verification proves.
      std::shared_ptr<const ContractTheorem> Contract;
      /// The verdict on the definedness of the function's contract, when it
      /// has clauses that may be undefined; its place in Diags.
      std::optional<size_t> ContractCheck;
      std::string Dump;
      std::string Archive;
      /// Ctrl-C came before the verification ended.
      bool Interrupted = false;
    };
    std::vector<FunctionRun> Runs(Functions.size());
    // The source manager caches its last line lookup.
    std::mutex SourceLock;
    auto verifyFunction = [&](size_t Index) {
      FunctionRun &Run = Runs[Index];
      std::vector<VerifyDiagnostic> &Diags = Run.Diags;
      bool &AllOk = Run.AllOk;
      bool &AnyFailed = Run.AnyFailed;
      std::set<std::string> &FailedCallers = Run.FailedCallers;
      std::set<std::string> &UndefinedSpecs = Run.UndefinedSpecs;
      auto &CallDependencies = Run.CallDependencies;
      std::set<std::string> &UnframedSpecs = Run.UnframedSpecs;
      std::set<std::string> &UnprovenPosts = Run.UnprovenPosts;
      auto &ProofDependencies = Run.ProofDependencies;
      auto &InductiveLines = Run.InductiveLines;
      // What stays unresolved for want of unfolding is explained in plain
      // words; a counterexample its check could not evaluate is kept for a
      // confirmation by proof, whose verdict is the next one reported.
      auto settle = [&](VerifyResult &R, const ObligationModule &Checked,
                        const VFunction &In, const std::string &Label,
                        BackendKind Kind) {
        if (R.Status == VerifyStatus::Unresolved &&
            !R.UncheckedApplication.empty())
          Run.Confirmations.push_back({Diags.size(),
                                       std::make_shared<ObligationModule>(
                                           copyObligationModule(Checked)),
                                       R, &In, Label, Kind});
        explainUnsettled(R, In, Checked);
      };
      // What the function's verification builds is bounded by the node
      // limit. Past it the function is too large: a verdict, which the
      // verdicts relying on its contract take into account.
      NodeBudget::Limit NodeLimit(Opts.MaxQueryNodes);
      auto tooLarge = [&](const VFunction &In,
                          const ObligationSizeError &Size) {
        VerifyResult Limited;
        Limited.Status = VerifyStatus::Unresolved;
        Limited.Reason = VerifyReason::QuerySizeLimit;
        Limited.BackendName = backendName(Opts.Backend);
        Limited.Message = Size.message();
        AllOk = false;
        AnyFailed = true;
        if (!Opts.LowerOnly && !In.IsProof)
          FailedCallers.insert(In.Identity);
        std::string Message =
            (Opts.LowerOnly ? lowerFailure(Opts.Backend) : std::string()) +
            In.Name + backendSuffix(Limited) + " (" + Limited.Message + ")";
        Diags.push_back({Opts.LowerOnly ? VerifyDiagnostic::Error
                                        : VerifyDiagnostic::Unresolved,
                         std::move(Message), In.DeclLoc, In.Name,
                         std::move(Limited)});
      };
      llvm::raw_string_ostream DumpStream(Run.Dump);
      llvm::raw_ostream *DumpOS = this->DumpOS ? &DumpStream : nullptr;
      std::unique_ptr<VerifyBackend> OwnBackend;
      VerifyBackend *Backend = SharedBackend.get();
      if (Parallel) {
        OwnBackend = createVerifyBackend(Opts.Backend, LeanOut, Opts.BMCUnroll,
                                         Execution, nullptr);
        Backend = OwnBackend.get();
      }
      // One budget for every query of this function.
      std::optional<std::chrono::steady_clock::time_point> Deadline;
      if (Opts.FunctionTimeoutMs != 0)
        Deadline = std::chrono::steady_clock::now() +
                   std::chrono::milliseconds(Opts.FunctionTimeoutMs);
      Backend->setDeadline(Deadline);
      // A spec's checks have no loops to bound: under BMC they are solved as
      // Z3 solves them (their archived modules keep the bound for replay).
      std::unique_ptr<VerifyBackend> OwnSpecBackend;
      VerifyBackend *SpecBackend = Backend;
      BackendKind SpecKind = Opts.Backend;
      if (Opts.Backend == BackendKind::BMC) {
        OwnSpecBackend = createVerifyBackend(BackendKind::Z3, nullptr, 0,
                                             Execution, nullptr);
        OwnSpecBackend->setDeadline(Deadline);
        SpecBackend = OwnSpecBackend.get();
        SpecKind = BackendKind::Z3;
      }
      auto SmokeBackend = createVerifyBackend(BackendKind::Z3, nullptr, 0,
                                              SmokeExecution, nullptr);
      // What else a failure shows. A counterexample that passes through a
      // loop starts from any state the loop's invariants allow, which no
      // execution need reach; unrolling the loops looks for an execution
      // that fails, or proves that none does.
      auto failureNotes = [&](const VFunction &F, const VerifyResult &Failure) {
        std::vector<std::string> Notes;
        auto at = [&](SourceLocation Loc) {
          const PresumedLoc Where = Ctx.getSourceManager().getPresumedLoc(Loc);
          return Where.isValid() ? std::to_string(Where.getLine()) + ":" +
                                       std::to_string(Where.getColumn())
                                 : std::string("?");
        };
        if (F.UnmeasuredLoop.isValid())
          Notes.push_back("the loop at " + at(F.UnmeasuredLoop) +
                          " has no cppverify::decreases: a proof would be "
                          "Unresolved (decreases.missing) until it has one");
        const auto Loop = llvm::find_if(Failure.Trace, [](const auto &Event) {
          return Event.Kind == DiagnosticTraceKind::Loop &&
                 Event.Active.value_or(false);
        });
        if (Loop == Failure.Trace.end() || !isDeductiveBackend(Opts.Backend) ||
            Failure.Reason != VerifyReason::Counterexample)
          return Notes;
        Notes.push_back(
            "the counterexample's state at the loop at " +
            (Loop->Source.isValid() ? std::to_string(Loop->Source.Line) + ":" +
                                          std::to_string(Loop->Source.Column)
                                    : std::string("?")) +
            " is any state its invariants allow, not necessarily one an "
            "execution reaches");
        if (Opts.ConfirmBound == 0 || !Failure.ObligationType)
          return Notes;
        VFunction Bounded = cloneVFunction(F);
        annotatePointerOrigins(Bounded);
        if (Opts.CheckUB && !F.TotalExpressions && instrumentUBChecks(Bounded))
          return Notes;
        SpecInliner(FnMap, Bounded.SpecFuel).prepareFunction(Bounded);
        // The search after a failure takes at most one query's time.
        Z3VerifyBackend Unroller(Execution, "bmc");
        std::optional<std::chrono::steady_clock::time_point> Until = Deadline;
        if (Opts.SolverTimeoutMs != 0) {
          const auto Slice = std::chrono::steady_clock::now() +
                             std::chrono::milliseconds(Opts.SolverTimeoutMs);
          if (!Until || Slice < *Until)
            Until = Slice;
        }
        Unroller.setDeadline(Until);
        auto iterations = [](unsigned Bound) {
          return std::to_string(Bound) +
                 (Bound == 1 ? " iteration" : " iterations");
        };
        // Unrolling keeps the function's checks, each copied into every
        // iteration it is in, but not the loops' invariants and measures:
        // the copies of the failed check are those of its kind at its place.
        auto copyOfFailure = [&](const VerifyResult &Result) {
          return Result.ObligationType == Failure.ObligationType &&
                 Result.Source.Line == Failure.Source.Line &&
                 Result.Source.Column == Failure.Source.Column &&
                 Result.Source.File == Failure.Source.File;
        };
        bool Unrolled = false;
        std::string Earlier;
        for (unsigned Bound = 0; Bound <= Opts.ConfirmBound; ++Bound) {
          VFunction Copy = LoopUnroller::unroll(Bounded, Bound);
          Passivizer Unrolling;
          Unrolling.setFunctionMap(InterfaceMap);
          auto Lowered = buildObligationModule(Unrolling.run(Copy));
          if (!Lowered) {
            llvm::consumeError(Lowered.takeError());
            return Notes;
          }
          auto Simplified = simplifyObligationModule(std::move(*Lowered));
          if (!Simplified) {
            llvm::consumeError(Simplified.takeError());
            return Notes;
          }
          ObligationModule Module = std::move(*Simplified);
          Module.BMCTransform = BMCTransformProvenance{Bound};
          annotateObligationSources(Module);
          bool Copies = false;
          bool CopiesHold = true;
          bool Unwound = true;
          // Every failure is reported, so a copy, or a loop's unwinding, is
          // solved in the executions that pass the failing checks before it:
          // one that fails an earlier check never reaches it. What holds
          // past another check that fails says so.
          std::vector<VerifyResult> Results =
              Unroller.verifyObligations(Module, /*ReportedFailures=*/0);
          size_t Last = 0;
          for (size_t I = 0; I != Results.size(); ++I)
            if (Results[I].ObligationType == ObligationKind::Unwinding ||
                copyOfFailure(Results[I]))
              Last = I;
          Earlier.clear();
          for (size_t I = 0; I != Last && Earlier.empty(); ++I)
            if (Results[I].Status == VerifyStatus::Failed &&
                Results[I].ObligationType &&
                Results[I].ObligationType != ObligationKind::Unwinding &&
                !copyOfFailure(Results[I]))
              Earlier = std::string(" (the ") +
                        obligationKindName(*Results[I].ObligationType) +
                        " check at " + std::to_string(Results[I].Source.Line) +
                        ":" + std::to_string(Results[I].Source.Column) +
                        " fails)";
          for (VerifyResult &Result : Results) {
            if (Result.ObligationType == ObligationKind::Unwinding) {
              Unwound &= Result.Status == VerifyStatus::Verified;
              continue;
            }
            if (!copyOfFailure(Result))
              continue;
            Copies = true;
            if (Result.Status == VerifyStatus::Failed &&
                Result.Reason == VerifyReason::Counterexample) {
              Notes.push_back(
                  "an execution fails this check " +
                  (Bound == 0
                       ? std::string("with no iteration of any loop")
                       : "within " + iterations(Bound) + " of each loop") +
                  (Result.Message.empty()
                       ? std::string()
                       : " (counterexample: " + Result.Message + ")"));
              return Notes;
            }
            CopiesHold &= Result.Status == VerifyStatus::Verified;
          }
          Unrolled |= Copies;
          // Unrolled once, every loop body holds a copy of each of its
          // checks, and a check after a loop has one from no iteration on;
          // a failure without a copy by then is of an invariant or a
          // measure, which unrolling drops at every bound.
          if (Bound >= 1 && !Unrolled)
            return Notes;
          if (!CopiesHold)
            return Notes;
          if (Copies && Unwound) {
            Notes.push_back(
                Earlier.empty()
                    ? "no execution fails this check: every loop ends within " +
                          iterations(Bound) +
                          ", and unrolling proves it there; the loops' "
                          "invariants are too weak for an unbounded proof"
                    : "no execution fails this check without failing an "
                      "earlier one first" +
                          Earlier +
                          ": those that pass the checks before it end every "
                          "loop within " +
                          iterations(Bound) + ", and unrolling proves it there");
            return Notes;
          }
        }
        if (Unrolled)
          Notes.push_back("no execution fails this check within " +
                          iterations(Opts.ConfirmBound) + " of each loop" +
                          (Earlier.empty()
                               ? std::string()
                               : " without failing an earlier one first" +
                                     Earlier));
        return Notes;
      };
      Passivizer P;
      P.setFunctionMap(InterfaceMap);
      auto proves = [&](PassiveProgram Smoke) {
        auto Lowered = buildObligationModule(Smoke, Opts.MaxQueryNodes);
        if (!Lowered) {
          llvm::consumeError(Lowered.takeError());
          return false;
        }
        auto Simplified = simplifyObligationModule(std::move(*Lowered));
        if (!Simplified) {
          llvm::consumeError(Simplified.takeError());
          return false;
        }
        return SmokeBackend->verify(*Simplified).Status ==
               VerifyStatus::Verified;
      };
      auto unreachable = [&](const PassiveProgram &Program, bool EntryOnly) {
        auto Lowered = buildObligationModule(
            smokeProgram(Program, EntryOnly ? 0 : Program.Stmts.size(),
                         falseGoal()),
            Opts.MaxQueryNodes);
        if (!Lowered) {
          llvm::consumeError(Lowered.takeError());
          return false;
        }
        auto Simplified = simplifyObligationModule(std::move(*Lowered));
        if (!Simplified) {
          llvm::consumeError(Simplified.takeError());
          return false;
        }
        return SmokeBackend->verify(*Simplified).Status ==
               VerifyStatus::Verified;
      };

      auto recordDependencies = [&](const VFunction &Verified,
                                    const ObligationModule &Used) {
        std::set<std::string> Specs = Verified.SpecDependencies;
        for (const auto &[Identity, Function] : Used.LogicFunctions)
          Specs.insert(Identity);
        Specs.erase(Verified.Identity);
        // A rule's proof uses its predicate's definition, not its unfolding.
        Specs.erase(Verified.InductiveRuleOf);
        SpecReliance Reliance{Diags.size() - 1, std::move(Specs),
                              Verified.FactsWithheld};
        Reliance.AssumedPosts = Used.AssumedPosts;
        Reliance.AssumedUnfoldings = Used.AssumedUnfoldings;
        Reliance.InductivePosts = Used.InductivePosts;
        // And those a solver was given for it, beyond its own text.
        if (Used.Given) {
          std::lock_guard<std::mutex> Guard(Used.Given->Lock);
          Reliance.AssumedPosts.insert(Used.Given->Postconditions.begin(),
                                       Used.Given->Postconditions.end());
          Reliance.AssumedUnfoldings.insert(Used.Given->Unfoldings.begin(),
                                            Used.Given->Unfoldings.end());
        }
        ProofDependencies.push_back(std::move(Reliance));
      };
      auto exportLeanFallback = [&](const ObligationModule &Module,
                                    llvm::StringRef Label,
                                    const VerifyResult &SolverResult) {
        return exportLeanFallbackTo(Diags, Module, Label, SolverResult);
      };
      auto emitObligationArchive =
          [&](const ObligationModule &Module) -> llvm::Error {
        llvm::Expected<std::string> Record = archiveRecord(Module);
        if (!Record)
          return Record.takeError();
        Run.Archive += *Record;
        return llvm::Error::success();
      };
      auto annotateObligationSources = [&](ObligationModule &Module) {
        std::lock_guard<std::mutex> Guard(SourceLock);
        this->annotateObligationSources(Module);
      };
      // A contract must be defined where it is evaluated (Dafny's
      // well-formedness check): its preconditions in order, and the
      // postconditions of a function whose body is not verified in every
      // state it may return in. It is checked as callers see it, so a lifted
      // helper's checks are reported at its call. The check is reported only
      // when it does not hold, and then the contract establishes nothing.
      auto checkContract = [&](const VFunction &Interface) {
        PassiveProgram Checks = P.contract(Interface);
        if (llvm::none_of(Checks.Stmts, [](const auto &S) {
              return S->K == PassiveStmt::Assert;
            }))
          return;
        const std::string Label = "contract of " + Interface.Name;
        auto unsettled = [&](VerifyDiagnostic::Kind Kind, std::string Message,
                             std::optional<VerifyResult> R = std::nullopt) {
          AllOk = false;
          AnyFailed = true;
          const SourceLocation Loc = R ? R->Location : Interface.DeclLoc;
          Diags.push_back(
              {Kind, std::move(Message), Loc, Interface.Name, std::move(R)});
          Run.ContractCheck = Diags.size() - 1;
        };
        auto Lowered = buildObligationModule(Checks);
        if (!Lowered)
          return unsettled(VerifyDiagnostic::Unresolved,
                           "obligation lowering failed for " + Label + " (" +
                               llvm::toString(Lowered.takeError()) + ")");
        auto Simplified = simplifyObligationModule(std::move(*Lowered));
        if (!Simplified)
          return unsettled(VerifyDiagnostic::Unresolved,
                           "obligation simplification failed for " + Label +
                               " (" + llvm::toString(Simplified.takeError()) +
                               ")");
        ObligationModule Module = std::move(*Simplified);
        if (Opts.Backend == BackendKind::BMC)
          Module.BMCTransform = BMCTransformProvenance{Opts.BMCUnroll};
        annotateObligationSources(Module);
        if (llvm::Error Error = emitObligationArchive(Module))
          return unsettled(VerifyDiagnostic::Error,
                           "cannot serialize obligation: " + Label + " (" +
                               llvm::toString(std::move(Error)) + ")");
        if (Opts.LowerOnly) {
          VerifyResult Result = lowerForBackend(Module, SpecKind, Execution);
          if (Result.Status != VerifyStatus::Lowered) {
            std::string Message =
                std::string(SpecKind == BackendKind::Z3 ? "Z3" : "backend") +
                " lowering failed for " + Label + backendSuffix(Result);
            if (!Result.Message.empty())
              Message += " (" + Result.Message + ")";
            unsettled(VerifyDiagnostic::Error, std::move(Message), Result);
          }
          return;
        }
        VerifyResult R = SpecBackend->verify(Module);
        settle(R, Module, Interface, Label, SpecKind);
        if (R.Status == VerifyStatus::Verified ||
            R.Status == VerifyStatus::Certified) {
          Diags.push_back(
              {R.Status == VerifyStatus::Verified ? VerifyDiagnostic::Verified
                                                  : VerifyDiagnostic::Certified,
               Label + backendSuffix(R), R.Location, Interface.Name, R});
          Diags.back().Quiet = true;
          recordDependencies(Interface, Module);
          Run.ContractCheck = Diags.size() - 1;
        } else if (R.Status == VerifyStatus::Exported) {
          Diags.push_back({VerifyDiagnostic::Exported,
                           "lean obligation: " + Label, R.Location,
                           Interface.Name, R});
          Run.ContractCheck = Diags.size() - 1;
        } else if (R.Status == VerifyStatus::Failed) {
          std::string Message = "verification failed: " + Label;
          if (!R.ObligationId.empty())
            Message += " [" + R.ObligationId + "]";
          if (!R.Message.empty())
            Message += " (counterexample: " + R.Message + ")";
          Message += backendSuffix(R);
          unsettled(VerifyDiagnostic::Error, std::move(Message), R);
        } else {
          const bool FallbackExported = R.Status == VerifyStatus::Unresolved &&
                                        exportLeanFallback(Module, Label, R);
          if (Opts.LeanCertify && FallbackExported) {
            Run.ContractCheck = Diags.size() - 1;
            return;
          }
          std::string Message = Label + backendSuffix(R);
          if (!R.Message.empty())
            Message += " (" + R.Message + ")";
          unsettled(VerifyDiagnostic::Unresolved, std::move(Message), R);
        }
      };
      for (const auto &Fn :
           llvm::ArrayRef<std::unique_ptr<VFunction>>(&Functions[Index], 1)) {
        // The value of a spec outside its when domain, or a spec of
        // <cppverify.h>: nothing to verify but a library spec's termination,
        // which is reported only if it fails.
        if (Fn->Uninterpreted || (Fn->IsBuiltin && !Fn->NeedsDecreasesCheck))
          continue;
        // What a function says depends on the definitions of the specs it
        // reaches, so one that reaches a spec the verifier does not
        // represent is not verified.
        std::string ReliesOn;
        for (const std::string &Spec : Fn->SpecDependencies)
          if (auto It = FnMap.find(Spec);
              It != FnMap.end() && It->second->UnsupportedConstruct)
            ReliesOn += (ReliesOn.empty() ? "" : ", ") + It->second->Name;
        if (!ReliesOn.empty()) {
          AllOk = false;
          VerifyResult R;
          R.Status = VerifyStatus::Unresolved;
          R.Reason = VerifyReason::UnsupportedConstruct;
          R.Message = "relies on " + ReliesOn +
                      ", which uses a construct the verifier does not support";
          VerifyDiagnostic D{VerifyDiagnostic::Unresolved,
                             Fn->Name + " [reason=construct.unsupported] (" +
                                 R.Message + ")",
                             Fn->DeclLoc, Fn->Name};
          D.Result = std::move(R);
          Diags.push_back(std::move(D));
          continue;
        }
        if (Fn->IsExternalContract) {
          if (Fn->IsTrusted)
            Diags.push_back({VerifyDiagnostic::Trusted,
                             Fn->Name + " (contract assumed, not verified)",
                             Fn->DeclLoc, Fn->Name});
          else if (!Fn->UnsupportedConstruct)
            Diags.push_back(
                {VerifyDiagnostic::Warning,
                 Fn->Name + " has a contract but no definition, so its callers "
                            "are not verified; mark the declaration "
                            "[[cppverify::trusted]] to assume the contract",
                 Fn->DeclLoc, Fn->Name});
          if (auto Error = InterfaceErrors.find(Fn->Identity);
              Error != InterfaceErrors.end()) {
            AllOk = false;
            AnyFailed = true;
            Diags.push_back(
                {VerifyDiagnostic::Error, Fn->Name + ": " + Error->second});
            Run.ContractCheck = Diags.size() - 1;
          } else if (!Fn->IsSpec) {
            checkContract(*InterfaceMap.at(Fn->Identity));
          }
          continue;
        }
        llvm::scope_exit MarkInterrupted(
            [&] { Run.Interrupted = interruptRequested(); });
        bool DumpedAny = false;
        auto dumpSep = [&]() {
          if (DumpedAny && MultiLayerDump)
            *DumpOS << "======\n";
          DumpedAny = true;
        };

        std::optional<VFunction> PreparedFn;
        std::optional<VFunction> UnrolledFn;
        std::optional<std::string> UBError;
        const VFunction *WorkFn = Fn.get();
        if (!Fn->IsSpec) {
          PreparedFn = cloneVFunction(*Fn);
          annotatePointerOrigins(*PreparedFn);
          // `valid(p, n)` is a recognized UB marker. Discover it before spec
          // preparation folds its deliberately trivial body to `true`.
          // A generated proof about specs is not C++ code.
          if (Fn->TotalExpressions) {
          } else if (Opts.CheckUB && (isDeductiveBackend(Opts.Backend) ||
                                      Opts.Backend == BackendKind::BMC ||
                                      Opts.Backend == BackendKind::Lean)) {
            UBError = instrumentUBChecks(*PreparedFn);
          } else if (usesValidMarker(*Fn))
            Diags.push_back(
                {VerifyDiagnostic::Warning,
                 "contract of " + Fn->Name +
                     " uses the valid(p, n) extent marker, but memory "
                     "checking is disabled (--no-check-ub); the marker folds "
                     "to `true` and declared extents are not assumed, so "
                     "results about heap contents may be spurious.",
                 SourceLocation(), Fn->Name});
          if (!UBError) {
            SpecInliner Inliner(FnMap, PreparedFn->SpecFuel);
            NodeBudget Inlining;
            if (isDeductiveBackend(Opts.Backend) ||
                Opts.Backend == BackendKind::Lean)
              Inliner.prepareFunctionAxiomatic(*PreparedFn);
            else
              Inliner.prepareFunction(*PreparedFn);
            if (Inlining.exceeded()) {
              tooLarge(*Fn, ObligationSizeError(
                                "its specs inlined as deep as their fuel",
                                Inlining.built(), Inlining.limit(),
                                "lower the fuel cppverify::reveal_with_fuel "
                                "gives, or raise the limit"));
              continue;
            }
          }
          WorkFn = &*PreparedFn;
          if (!UBError && Opts.Backend == BackendKind::BMC && Opts.LowerOnly) {
            UnrolledFn = LoopUnroller::unroll(*PreparedFn, Opts.BMCUnroll);
            WorkFn = &*UnrolledFn;
          }
        } else if (Opts.CheckUB && !Fn->IsBuiltin) {
          UBError = misplacedValidMarker(*Fn);
        }

        if (UBError) {
          AllOk = false;
          AnyFailed = true;
          if (!Fn->IsProof)
            FailedCallers.insert(Fn->Identity);
          Diags.push_back(
              {VerifyDiagnostic::Error, Fn->Name + ": " + *UBError});
          continue;
        }

        if (Fn->IsSpec && !Fn->Reads.empty()) {
          std::string Missing;
          PassiveProgram ReadsPP =
              withClauseProofs(buildReadsChecks(*Fn, FnMap, Missing), *Fn,
                               {VFunction::ClauseProof::Reads}, FnMap);
          UnframedSpecs.insert(Fn->Identity);
          std::optional<ObligationModule> ReadsModule;
          std::string ReadsError;
          if (!Missing.empty()) {
            ReadsError = "calls " + Missing +
                         ", which reads the heap without a reads clause";
          } else if (auto Lowered =
                         buildObligationModule(ReadsPP, Opts.MaxQueryNodes)) {
            if (auto Simplified = simplifyObligationModule(std::move(*Lowered)))
              ReadsModule = std::move(*Simplified);
            else
              ReadsError = llvm::toString(Simplified.takeError());
          } else {
            ReadsError = llvm::toString(Lowered.takeError());
          }
          if (!ReadsModule) {
            AllOk = false;
            AnyFailed = true;
            Diags.push_back(
                {VerifyDiagnostic::Error,
                 "spec reads failed: " + Fn->Name + " (" + ReadsError + ")",
                 SourceLocation(), Fn->Name});
          } else if (Opts.Backend == BackendKind::BMC) {
            // Kept for archive replay; the check runs as Z3 runs it.
            ReadsModule->BMCTransform = BMCTransformProvenance{Opts.BMCUnroll};
          }
          if (ReadsModule) {
            annotateObligationSources(*ReadsModule);
            if (llvm::Error Error = emitObligationArchive(*ReadsModule)) {
              AllOk = false;
              AnyFailed = true;
              Diags.push_back(
                  {VerifyDiagnostic::Error,
                   "cannot serialize reads obligation: " + Fn->Name + " (" +
                       llvm::toString(std::move(Error)) + ")"});
              continue;
            }
            if (Opts.LowerOnly) {
              VerifyResult R =
                  lowerForBackend(*ReadsModule, SpecKind, Execution);
              if (R.Status == VerifyStatus::Lowered) {
                UnframedSpecs.erase(Fn->Identity);
                Diags.push_back({VerifyDiagnostic::Lowered,
                                 "spec reads: " + Fn->Name, R.Location,
                                 Fn->Name, R});
              } else {
                AllOk = false;
                AnyFailed = true;
                Diags.push_back({VerifyDiagnostic::Error,
                                 "lowering failed for reads: " + Fn->Name +
                                     backendSuffix(R),
                                 R.Location, Fn->Name, R});
              }
            } else {
              VerifyResult R = SpecBackend->verify(*ReadsModule);
              settle(R, *ReadsModule, *Fn, "spec reads", SpecKind);
              if (R.Status == VerifyStatus::Verified ||
                  R.Status == VerifyStatus::Exported) {
                UnframedSpecs.erase(Fn->Identity);
                Diags.push_back({R.Status == VerifyStatus::Verified
                                     ? VerifyDiagnostic::Verified
                                     : VerifyDiagnostic::Exported,
                                 "spec reads: " + Fn->Name, R.Location,
                                 Fn->Name, R});
                recordDependencies(*Fn, *ReadsModule);
                ProofDependencies.back().Establishes = Fn->Identity;
                ProofDependencies.back().Facts = ReadsFact;
                ProofDependencies.back().Callees =
                    clauseProofCallees(*Fn, {VFunction::ClauseProof::Reads});
              } else {
                AllOk = false;
                AnyFailed = true;
                const bool IsUnresolved = R.Status == VerifyStatus::Unresolved;
                std::string Message =
                    std::string("spec reads ") +
                    (IsUnresolved ? "unresolved: " : "failed: ") + Fn->Name +
                    backendSuffix(R);
                if (!R.Message.empty())
                  Message += " (" + R.Message + ")";
                Diags.push_back({IsUnresolved ? VerifyDiagnostic::Unresolved
                                              : VerifyDiagnostic::Error,
                                 std::move(Message), R.Location, Fn->Name, R});
              }
            }
          }
        }

        // An inductive predicate's line stands for its rules, which its
        // generated proofs establish.
        if (Fn->Unfolding) {
          Diags.push_back({Opts.LowerOnly ? VerifyDiagnostic::Lowered
                           : Opts.Backend == BackendKind::Lean
                               ? VerifyDiagnostic::Exported
                               : VerifyDiagnostic::Verified,
                           "inductive predicate: " + Fn->Name});
          InductiveLines.emplace_back(Diags.size() - 1, Fn->Identity);
        }
        const bool Step = !Fn->InductiveStepOf.empty();
        if (Fn->IsSpec && !Fn->NeedsDecreasesCheck &&
            !Fn->Postconditions.empty() && !Step) {
          UnprovenPosts.insert(Fn->Identity);
          std::optional<ObligationModule> PostModule;
          std::string PostError;
          if (auto Lowered = buildObligationModule(
                  withClauseProofs(buildSpecPostChecks(*Fn, FnMap), *Fn,
                                   {VFunction::ClauseProof::Post}, FnMap),
                  Opts.MaxQueryNodes)) {
            if (auto Simplified = simplifyObligationModule(std::move(*Lowered)))
              PostModule = std::move(*Simplified);
            else
              PostError = llvm::toString(Simplified.takeError());
          } else {
            PostError = llvm::toString(Lowered.takeError());
          }
          if (!PostModule) {
            AllOk = false;
            AnyFailed = true;
            Diags.push_back({VerifyDiagnostic::Unresolved,
                             "obligation lowering failed for spec post: " +
                                 Fn->Name + " (" + PostError + ")"});
            continue;
          }
          if (Opts.Backend == BackendKind::BMC)
            PostModule->BMCTransform = BMCTransformProvenance{Opts.BMCUnroll};
          annotateObligationSources(*PostModule);
          if (llvm::Error Error = emitObligationArchive(*PostModule)) {
            AllOk = false;
            AnyFailed = true;
            Diags.push_back(
                {VerifyDiagnostic::Error,
                 "cannot serialize spec post obligation: " + Fn->Name + " (" +
                     llvm::toString(std::move(Error)) + ")"});
            continue;
          }
          if (Opts.LowerOnly) {
            VerifyResult R = lowerForBackend(*PostModule, SpecKind, Execution);
            if (R.Status == VerifyStatus::Lowered) {
              UnprovenPosts.erase(Fn->Identity);
              Diags.push_back({VerifyDiagnostic::Lowered,
                               "spec post: " + Fn->Name, R.Location, Fn->Name,
                               R});
            } else {
              AllOk = false;
              AnyFailed = true;
              Diags.push_back({VerifyDiagnostic::Error,
                               "lowering failed for spec post: " + Fn->Name +
                                   backendSuffix(R),
                               R.Location, Fn->Name, R});
            }
            continue;
          }
          VerifyResult R = SpecBackend->verify(*PostModule);
          settle(R, *PostModule, *Fn, "spec post", SpecKind);
          if (R.Status == VerifyStatus::Verified ||
              R.Status == VerifyStatus::Exported) {
            UnprovenPosts.erase(Fn->Identity);
            Diags.push_back({R.Status == VerifyStatus::Verified
                                 ? VerifyDiagnostic::Verified
                                 : VerifyDiagnostic::Exported,
                             "spec post: " + Fn->Name, R.Location, Fn->Name,
                             R});
            recordDependencies(*Fn, *PostModule);
            ProofDependencies.back().Establishes = Fn->Identity;
            ProofDependencies.back().Facts = PostFact;
            // An inductive predicate's post comes from its step's; the
            // predicates defined with it give their unfoldings only.
            if (auto Step = FnMap.find(Fn->Identity + "::step");
                Fn->Unfolding && Step != FnMap.end())
              for (llvm::StringRef Member : Step->second->RecursionGroup)
                if (Member.ends_with("::step"))
                  ProofDependencies.back().PostsWithheld.insert(
                      Member.drop_back(6).str());
            ProofDependencies.back().Callees =
                clauseProofCallees(*Fn, {VFunction::ClauseProof::Post});
          } else {
            AllOk = false;
            AnyFailed = true;
            const bool IsUnresolved = R.Status == VerifyStatus::Unresolved;
            std::string Message = std::string("spec post ") +
                                  (IsUnresolved ? "unresolved: " : "failed: ") +
                                  Fn->Name + backendSuffix(R);
            if (!R.Message.empty())
              Message += " (" + R.Message + ")";
            Diags.push_back({IsUnresolved ? VerifyDiagnostic::Unresolved
                                          : VerifyDiagnostic::Error,
                             std::move(Message), R.Location, Fn->Name, R});
          }
          continue;
        }

        if (Fn->IsSpec && !Fn->NeedsDecreasesCheck && !Step) {
          // Nothing is solved for a spec axiom, which is listed only with
          // --verbose.
          MarkInterrupted.release();
          if (!Opts.Verbose)
            continue;
          const VerifyDiagnostic::Kind Kind =
              Opts.LowerOnly ? VerifyDiagnostic::Lowered
                             : (Opts.Backend == BackendKind::Lean
                                    ? VerifyDiagnostic::Exported
                                    : VerifyDiagnostic::Verified);
          if (Fn->IsConstexprSpec)
            Diags.push_back({Kind, "constexpr spec axiom: " + Fn->Name});
          else if (!Fn->Unfolding)
            Diags.push_back({Kind, "spec axiom: " + Fn->Name});
          else
            continue;
          Diags.back().Axiom = true;
          continue;
        }

        // Executable and proof recursion is checked at each call in the
        // function's own obligations; a spec's definition cannot help prove its
        // termination, so it is checked separately.
        // A step function of an inductive predicate terminates whatever its
        // postconditions say, so they are proved apart, after its
        // termination: by induction on the height, with its definition known,
        // which that check establishes. Only a failure is reported.
        auto runInduction = [&] {
          if (!Step || Fn->Postconditions.empty())
            return;
          UnprovenPosts.insert(Fn->Identity);
          const std::string Label = "spec post by induction";
          std::optional<ObligationModule> Induction;
          std::string Error;
          if (auto Lowered = buildObligationModule(
                  withClauseProofs(buildInductionChecks(*Fn, FnMap), *Fn,
                                   {VFunction::ClauseProof::Post}, FnMap),
                  Opts.MaxQueryNodes)) {
            if (auto Simplified = simplifyObligationModule(std::move(*Lowered)))
              Induction = std::move(*Simplified);
            else
              Error = llvm::toString(Simplified.takeError());
          } else {
            Error = llvm::toString(Lowered.takeError());
          }
          if (!Induction) {
            AllOk = false;
            AnyFailed = true;
            Diags.push_back({VerifyDiagnostic::Unresolved,
                             "obligation lowering failed for " + Label + ": " +
                                 Fn->InductiveStepOf + " (" + Error + ")"});
          } else {
            if (Opts.Backend == BackendKind::BMC)
              Induction->BMCTransform = BMCTransformProvenance{Opts.BMCUnroll};
            annotateObligationSources(*Induction);
            if (llvm::Error Error = emitObligationArchive(*Induction)) {
              AllOk = false;
              AnyFailed = true;
              Diags.push_back({VerifyDiagnostic::Error,
                               "cannot serialize " + Label + " obligation: " +
                                   Fn->InductiveStepOf + " (" +
                                   llvm::toString(std::move(Error)) + ")"});
            } else if (Opts.LowerOnly) {
              VerifyResult R = lowerForBackend(*Induction, SpecKind, Execution);
              if (R.Status == VerifyStatus::Lowered) {
                UnprovenPosts.erase(Fn->Identity);
              } else {
                AllOk = false;
                AnyFailed = true;
                Diags.push_back({VerifyDiagnostic::Error,
                                 "lowering failed for " + Label + ": " +
                                     Fn->InductiveStepOf + backendSuffix(R),
                                 R.Location, Fn->Name, R});
              }
            } else {
              VerifyResult R = SpecBackend->verify(*Induction);
              settle(R, *Induction, *Fn, "spec post by induction", SpecKind);
              if (R.Status == VerifyStatus::Verified ||
                  R.Status == VerifyStatus::Exported) {
                UnprovenPosts.erase(Fn->Identity);
                Diags.push_back({R.Status == VerifyStatus::Verified
                                     ? VerifyDiagnostic::Verified
                                     : VerifyDiagnostic::Exported,
                                 Label + ": " + Fn->InductiveStepOf, R.Location,
                                 Fn->Name, R});
                Diags.back().Quiet = true;
                // The proof uses the definition, so it rests on termination,
                // and the predicates of the group through their unfoldings.
                recordDependencies(*Fn, *Induction);
                SpecReliance &Reliance = ProofDependencies.back();
                Reliance.Specs.insert(Fn->Identity);
                Reliance.Establishes = Fn->Identity;
                Reliance.Facts = PostFact;
                Reliance.Callees =
                    clauseProofCallees(*Fn, {VFunction::ClauseProof::Post});
                std::set<std::string> Group = Fn->RecursionGroup;
                Group.insert(Fn->Identity);
                for (llvm::StringRef Member : Group)
                  if (Member.ends_with("::step"))
                    Reliance.PostsWithheld.insert(Member.drop_back(6).str());
              } else {
                AllOk = false;
                AnyFailed = true;
                const bool IsUnresolved = R.Status == VerifyStatus::Unresolved;
                std::string Message =
                    Label + (IsUnresolved ? " unresolved: " : " failed: ") +
                    Fn->InductiveStepOf + backendSuffix(R);
                if (!R.Message.empty())
                  Message += " (" + R.Message + ")";
                Diags.push_back({IsUnresolved ? VerifyDiagnostic::Unresolved
                                              : VerifyDiagnostic::Error,
                                 std::move(Message), R.Location, Fn->Name, R});
              }
            }
          }
        };

        if (Step && !Fn->NeedsDecreasesCheck) {
          runInduction();
          continue;
        }
        if (Fn->NeedsDecreasesCheck && Fn->IsSpec) {
          std::optional<VFunction> Bare;
          if (Step && !Fn->Postconditions.empty()) {
            Bare = cloneVFunction(*Fn);
            Bare->Postconditions.clear();
            Bare->PostconditionKinds.clear();
          }
          PassiveProgram DecPP = withClauseProofs(
              buildDecreasesChecks(Bare ? *Bare : *Fn, FnMap),
              Bare ? *Bare : *Fn,
              Bare ? std::set<VFunction::ClauseProof::
                                  Kind>{VFunction::ClauseProof::Decreases}
                   : std::set<VFunction::ClauseProof::
                                  Kind>{VFunction::ClauseProof::Post,
                                        VFunction::ClauseProof::Decreases},
              FnMap);
          auto DecModuleOrErr =
              buildObligationModule(DecPP, Opts.MaxQueryNodes);
          // A spec's postcondition is proved with its termination.
          const std::string &Shown = Step ? Fn->InductiveStepOf : Fn->Name;
          const bool Quiet = Fn->IsBuiltin || Step;
          const std::string DecLabel = !Step && !Fn->Postconditions.empty()
                                           ? "spec decreases and post: "
                                           : "spec decreases: ";
          UndefinedSpecs.insert(Fn->Identity);
          if (!Step && !Fn->Postconditions.empty())
            UnprovenPosts.insert(Fn->Identity);
          if (!DecModuleOrErr) {
            AllOk = false;
            AnyFailed = true;
            Diags.push_back(
                {VerifyDiagnostic::Unresolved,
                 "obligation lowering failed for decreases: " + Shown + " (" +
                     llvm::toString(DecModuleOrErr.takeError()) + ")"});
            runInduction();
            continue;
          }
          ObligationSimplificationStats DecSimplification;
          auto SimplifiedDecModule = simplifyObligationModule(
              std::move(*DecModuleOrErr), &DecSimplification);
          if (!SimplifiedDecModule) {
            AllOk = false;
            AnyFailed = true;
            Diags.push_back(
                {VerifyDiagnostic::Unresolved,
                 "obligation simplification failed for decreases: " + Shown +
                     " (" + llvm::toString(SimplifiedDecModule.takeError()) +
                     ")"});
            runInduction();
            continue;
          }
          ObligationModule DecModule = std::move(*SimplifiedDecModule);
          if (Opts.Backend == BackendKind::BMC)
            DecModule.BMCTransform = BMCTransformProvenance{Opts.BMCUnroll};
          annotateObligationSources(DecModule);
          if (llvm::Error Error = emitObligationArchive(DecModule)) {
            AllOk = false;
            AnyFailed = true;
            Diags.push_back({VerifyDiagnostic::Error,
                             "cannot serialize decreases obligation: " + Shown +
                                 " (" + llvm::toString(std::move(Error)) +
                                 ")"});
            runInduction();
            continue;
          }
          if (Opts.LowerOnly) {
            VerifyResult DR = lowerForBackend(DecModule, SpecKind, Execution);
            if (DR.Status != VerifyStatus::Lowered) {
              AllOk = false;
              AnyFailed = true;
              std::string Message =
                  std::string(Opts.Backend == BackendKind::Z3 ||
                                      Opts.Backend == BackendKind::BMC
                                  ? "Z3"
                                  : "backend") +
                  " lowering failed for decreases: " + Shown;
              Message += backendSuffix(DR);
              if (!DR.Message.empty())
                Message += " (" + DR.Message + ")";
              Diags.push_back({VerifyDiagnostic::Error, std::move(Message),
                               DR.Location, Fn->Name, std::move(DR)});
              runInduction();
              continue;
            }
            if (Fn->IsSpec) {
              if (!Step)
                UnprovenPosts.erase(Fn->Identity);
              if (!Quiet)
                Diags.push_back({VerifyDiagnostic::Lowered, DecLabel + Shown,
                                 SourceLocation(), Fn->Name, DR});
              runInduction();
              continue;
            }
          } else {
            if (LeanFallbackBackend)
              LeanRunGroups.insert(leanProjectGroup(DecModule));
            VerifyResult R = SpecBackend->verify(DecModule);
            if (Fn->IsSpec && (R.Reason == VerifyReason::SpecHidden ||
                               R.Reason == VerifyReason::SpecFuel)) {
              // The function is opaque in its own termination check.
              std::string Rule =
                  "a definition cannot be used to prove its own termination, "
                  "so every recursive call of " +
                  Fn->Name +
                  " must decrease the measure whatever its other calls return";
              R.Message = R.Reason == VerifyReason::SpecHidden
                              ? std::move(Rule)
                              : Rule + " (" + R.Message + ")";
            }
            // What the check establishes once proved: by the solver now, or
            // by Lean when certification settles its verdict, which until
            // then leaves the spec undefined.
            auto establishSpec = [&] {
              recordDependencies(*Fn, DecModule);
              SpecReliance &Reliance = ProofDependencies.back();
              Reliance.Establishes = Fn->Identity;
              Reliance.Facts =
                  DefinitionFact | (Step ? 0U : unsigned(PostFact));
              Reliance.Callees =
                  Step ? clauseProofCallees(*Fn,
                                            {VFunction::ClauseProof::Decreases})
                       : clauseProofCallees(*Fn,
                                            {VFunction::ClauseProof::Decreases,
                                             VFunction::ClauseProof::Post});
            };
            if (R.Status == VerifyStatus::Exported) {
              Diags.push_back({VerifyDiagnostic::Exported,
                               "decreases: " + Shown, R.Location, Fn->Name, R});
              Diags.back().Quiet = Quiet;
              if (Fn->IsSpec) {
                establishSpec();
                runInduction();
                continue;
              }
            } else if (R.Status == VerifyStatus::Verified) {
              if (Fn->IsSpec) {
                UndefinedSpecs.erase(Fn->Identity);
                if (!Step)
                  UnprovenPosts.erase(Fn->Identity);
                Diags.push_back({VerifyDiagnostic::Verified, DecLabel + Shown,
                                 R.Location, Fn->Name, R});
                Diags.back().Quiet = Quiet;
                establishSpec();
                runInduction();
                continue;
              }
            } else {
              const bool IsUnresolved = R.Status == VerifyStatus::Unresolved;
              const bool FallbackExported =
                  IsUnresolved &&
                  exportLeanFallback(DecModule, "decreases: " + Fn->Name, R);
              if (Opts.LeanCertify && FallbackExported) {
                if (Fn->IsSpec) {
                  establishSpec();
                  runInduction();
                  continue;
                }
              } else {
                AllOk = false;
                AnyFailed = true;
                if (!Fn->IsProof)
                  FailedCallers.insert(Fn->Identity);
                std::string Message =
                    std::string(Fn->IsSpec
                                    ? DecLabel.substr(0, DecLabel.size() - 2) +
                                          " "
                                    : "decreases ") +
                    (IsUnresolved ? "unresolved: " : "failed: ") + Shown +
                    backendSuffix(R);
                if (!R.Message.empty())
                  Message += " (" + R.Message + ")";
                Diags.push_back({IsUnresolved ? VerifyDiagnostic::Unresolved
                                              : VerifyDiagnostic::Error,
                                 std::move(Message), R.Location, Fn->Name, R});
                runInduction();
                continue;
              }
            }
          }
        }

        if (!Fn->IsSpec && !Fn->TotalExpressions)
          checkContract(*InterfaceMap.at(Fn->Identity));

        std::optional<PassiveProgram> BMCProgram;
        std::optional<ObligationModule> BMCModule;
        std::optional<VerifyResult> BMCResult;
        ObligationSimplificationStats BMCSimplification;
        if (Opts.Backend == BackendKind::BMC && !Opts.LowerOnly) {
          std::vector<unsigned> ExploredBounds;
          uint64_t CacheHits = 0;
          uint64_t CacheMisses = 0;
          uint64_t CacheErrors = 0;
          uint64_t ReusedQueries = 0;
          std::string CacheError;
          bool PreparationFailed = false;
          for (unsigned Bound = 0;; ++Bound) {
            UnrolledFn = LoopUnroller::unroll(*PreparedFn, Bound);
            Passivizer BoundPassivizer;
            BoundPassivizer.setFunctionMap(InterfaceMap);
            PassiveProgram BoundProgram = BoundPassivizer.run(*UnrolledFn);
            auto BoundModuleOrErr =
                buildObligationModule(BoundProgram, Opts.MaxQueryNodes);
            if (!BoundModuleOrErr) {
              AllOk = false;
              AnyFailed = true;
              Diags.push_back(
                  {VerifyDiagnostic::Unresolved,
                   "BMC obligation lowering failed at bound " +
                       std::to_string(Bound) + ": " + Fn->Name + " (" +
                       llvm::toString(BoundModuleOrErr.takeError()) + ")"});
              PreparationFailed = true;
              break;
            }
            ObligationSimplificationStats BoundSimplification;
            auto SimplifiedBoundModule = simplifyObligationModule(
                std::move(*BoundModuleOrErr), &BoundSimplification);
            if (!SimplifiedBoundModule) {
              AllOk = false;
              AnyFailed = true;
              Diags.push_back(
                  {VerifyDiagnostic::Unresolved,
                   "BMC obligation simplification failed at bound " +
                       std::to_string(Bound) + ": " + Fn->Name + " (" +
                       llvm::toString(SimplifiedBoundModule.takeError()) +
                       ")"});
              PreparationFailed = true;
              break;
            }
            ObligationModule BoundModule = std::move(*SimplifiedBoundModule);
            BoundModule.BMCTransform = BMCTransformProvenance{Bound};
            annotateObligationSources(BoundModule);
            VerifyResult Result = Backend->verify(BoundModule);
            ExploredBounds.push_back(Bound);
            CacheHits += Result.CacheHits;
            CacheMisses += Result.CacheMisses;
            CacheErrors += Result.CacheErrors;
            ReusedQueries += Result.ReusedQueries;
            if (CacheError.empty() && !Result.CacheError.empty())
              CacheError = Result.CacheError;

            if (Result.Status != VerifyStatus::BoundedSafe ||
                Bound == Opts.BMCUnroll) {
              Result.CacheHits = CacheHits;
              Result.CacheMisses = CacheMisses;
              Result.CacheErrors = CacheErrors;
              Result.CacheError = std::move(CacheError);
              Result.ReusedQueries = ReusedQueries;
              Result.ExploredBounds = std::move(ExploredBounds);
              WorkFn = &*UnrolledFn;
              BMCProgram = std::move(BoundProgram);
              BMCModule = std::move(BoundModule);
              BMCResult = std::move(Result);
              BMCSimplification = BoundSimplification;
              break;
            }
          }
          if (PreparationFailed)
            continue;
        }

        if (DumpLayers & LayerVCR) {
          dumpSep();
          dumpVFunction(*WorkFn, *DumpOS);
        }

        PassiveProgram PP =
            BMCProgram ? std::move(*BMCProgram) : P.run(*WorkFn);
        if (DumpLayers & LayerPassive) {
          dumpSep();
          dumpPassiveProgram(Fn->Name, PP, *DumpOS);
        }

        ObligationSimplificationStats Simplification;
        ObligationModule Module;
        if (BMCModule) {
          Module = std::move(*BMCModule);
          Simplification = BMCSimplification;
        } else {
          auto ModuleOrErr = buildObligationModule(PP, Opts.MaxQueryNodes);
          if (!ModuleOrErr) {
            AllOk = false;
            AnyFailed = true;
            bool Limited = false;
            llvm::Error Error = llvm::handleErrors(
                ModuleOrErr.takeError(), [&](const ObligationSizeError &Size) {
                  tooLarge(*Fn, Size);
                  Limited = true;
                });
            if (Limited)
              llvm::consumeError(std::move(Error));
            else
              Diags.push_back({VerifyDiagnostic::Unresolved,
                               "obligation lowering failed: " + Fn->Name +
                                   " (" + llvm::toString(std::move(Error)) +
                                   ")"});
            continue;
          }
          auto SimplifiedModule = simplifyObligationModule(
              std::move(*ModuleOrErr), &Simplification);
          if (!SimplifiedModule) {
            AllOk = false;
            AnyFailed = true;
            Diags.push_back(
                {VerifyDiagnostic::Unresolved,
                 "obligation simplification failed: " + Fn->Name + " (" +
                     llvm::toString(SimplifiedModule.takeError()) + ")"});
            continue;
          }
          Module = std::move(*SimplifiedModule);
          if (Opts.Backend == BackendKind::BMC)
            Module.BMCTransform = BMCTransformProvenance{Opts.BMCUnroll};
          annotateObligationSources(Module);
        }
        const size_t ArchiveMark = Run.Archive.size();
        if (llvm::Error Error = emitObligationArchive(Module)) {
          AllOk = false;
          AnyFailed = true;
          Diags.push_back({VerifyDiagnostic::Error,
                           "cannot serialize obligation: " + Fn->Name + " (" +
                               llvm::toString(std::move(Error)) + ")"});
          continue;
        }

        if (DumpLayers & LayerVC) {
          dumpSep();
          dumpVC(Module, *DumpOS, &Simplification);
        }

        if (DumpLayers & LayerZ3) {
          if (DumpLayers & LayerZ3)
            dumpSep();
          VerifyResult Lowered =
              lowerObligationModule(Module, DumpOS, Execution);
          if (Lowered.Status != VerifyStatus::Lowered) {
            AllOk = false;
            AnyFailed = true;
            std::string Message = "Z3 lowering failed: " + Fn->Name;
            Message += backendSuffix(Lowered);
            if (!Lowered.Message.empty())
              Message += " (" + Lowered.Message + ")";
            Diags.push_back({VerifyDiagnostic::Error, std::move(Message),
                             Lowered.Location, Fn->Name, std::move(Lowered)});
            continue;
          }
        }
        if (Opts.LowerOnly) {
          VerifyResult Lowered =
              lowerForBackend(Module, Opts.Backend, Execution);
          if (Lowered.Status != VerifyStatus::Lowered) {
            AllOk = false;
            AnyFailed = true;
            std::string Message = lowerFailure(Opts.Backend) + Fn->Name;
            Message += backendSuffix(Lowered);
            if (!Lowered.Message.empty())
              Message += " (" + Lowered.Message + ")";
            Diags.push_back({VerifyDiagnostic::Error, std::move(Message),
                             Lowered.Location, Fn->Name, std::move(Lowered)});
            continue;
          }
        }
        if (DumpLayers)
          DumpOS->flush();

        if (Opts.LowerOnly) {
          VerifyResult Result;
          Result.Status = VerifyStatus::Lowered;
          Result.BackendName = backendName(Opts.Backend);
          Diags.push_back({VerifyDiagnostic::Lowered, Fn->Name,
                           SourceLocation(), Fn->Name, std::move(Result)});
          continue;
        }

        if (LeanFallbackBackend)
          LeanRunGroups.insert(leanProjectGroup(Module));
        VerifyResult R =
            BMCResult ? std::move(*BMCResult) : Backend->verify(Module);
        // Every unfolding depth gives the solver only proved facts, so the
        // first decided verdict among depths stands; a counterexample is
        // checked against the true definitions at any depth.
        auto atDepth = [&](unsigned Depth, bool WithFuel) {
          Passivizer Again;
          Again.setFunctionMap(InterfaceMap);
          Again.setUnfoldingDepth(Depth, WithFuel);
          auto Built =
              buildObligationModule(Again.run(*WorkFn), Opts.MaxQueryNodes);
          if (!Built) {
            llvm::consumeError(Built.takeError());
            return false;
          }
          auto Simplified = simplifyObligationModule(std::move(*Built));
          if (!Simplified) {
            llvm::consumeError(Simplified.takeError());
            return false;
          }
          annotateObligationSources(*Simplified);
          VerifyResult Decided = Backend->verify(*Simplified);
          // Short of a verdict, a finding that no unfolding can settle the
          // goal is the more precise reason, and ends the search.
          if (Decided.Status != VerifyStatus::Verified &&
              Decided.Status != VerifyStatus::Failed &&
              !(Decided.Status == VerifyStatus::Unresolved &&
                Decided.InductionOnly && !R.InductionOnly))
            return false;
          Module = std::move(*Simplified);
          R = std::move(Decided);
          Run.Archive.resize(ArchiveMark);
          if (llvm::Error Error = emitObligationArchive(Module))
            llvm::consumeError(std::move(Error));
          return true;
        };
        auto fuelOf = [&](const std::string &Predicate) {
          auto It = WorkFn->SpecFuel.find(Predicate);
          return It == WorkFn->SpecFuel.end() ? 1U : std::max(1U, It->second);
        };
        const std::set<std::string> Unfolded = Module.AssumedUnfoldings;
        // A verdict that waits on inductive predicates gets them unfolded one
        // level deeper at a time, as Stainless unrolls recursive functions.
        if (!BMCResult && R.Status == VerifyStatus::Unresolved &&
            !R.InductionOnly &&
            (R.Reason == VerifyReason::SpecFuel ||
             R.Reason == VerifyReason::SpecHidden ||
             R.Reason == VerifyReason::UncheckedCounterexample))
          for (unsigned Depth = 2; Depth <= MaxUnfoldingDepth; ++Depth)
            if (llvm::any_of(Unfolded,
                             [&](const std::string &Predicate) {
                               return fuelOf(Predicate) < Depth;
                             }) &&
                atDepth(Depth, /*WithFuel=*/true))
              break;
        // Deeper unfoldings under a quantifier are quantified facts, which can
        // keep the solver from finding a model: after reveal_with_fuel, the
        // fewest unfoldings are tried too.
        if (!BMCResult && R.Status == VerifyStatus::Unresolved &&
            llvm::any_of(Unfolded, [&](const std::string &Predicate) {
              return fuelOf(Predicate) > 1;
            }))
          atDepth(1, /*WithFuel=*/false);
        // A member of a cluster sees another's definition only below its
        // measure, whatever it reveals: say so where a proof needs one.
        if (R.Status == VerifyStatus::Unresolved &&
            R.Reason == VerifyReason::SpecHidden) {
          std::string Names;
          for (const std::string &Identity : WorkFn->Cluster)
            if (auto It = InterfaceMap.find(Identity);
                It != InterfaceMap.end() && It->second->IsSpec &&
                WorkFn->HiddenSpecs.count(Identity) &&
                R.Message.find(It->second->Name) != std::string::npos)
              Names += (Names.empty() ? "" : ", ") + It->second->Name;
          if (!Names.empty()) {
            if (size_t At = R.Message.find("; reveal it or state a lemma");
                At != std::string::npos)
              R.Message.erase(At, std::strlen("; reveal it or state a lemma"));
            R.Message +=
                "; " + Names + " shares a cluster with " + Fn->Name +
                ", whose members use each other's definitions only "
                "where the measure is lower: give " +
                Names +
                " a lower measure at these arguments, as "
                "cppverify::decreases(n, 0) against cppverify::decreases(n, 1)";
          }
        }
        settle(R, Module, *Fn, "verification", Opts.Backend);
        // A proof rests on what its module uses: callee contracts and spec
        // facts. So does a Lean proof, which certification checks after
        // every function, and whose verdict waits for it (Pending).
        auto establish = [&](bool Pending) {
          // The module verified, the bounded one under BMC (moved into it).
          const size_t Verdict = Diags.size() - 1;
          recordDependencies(*Fn, Module);
          if (Fn->IsProof && !Fn->IsSpec)
            Run.Contract = Module.Contract;
          std::set<std::string> Callees;
          collectCallees(Fn->Body, Callees);
          CallDependencies.emplace_back(Verdict, Fn->Identity,
                                        std::move(Callees));
          const bool Rule = !Fn->InductiveRuleOf.empty();
          if (!Pending)
            Diags[Verdict].Quiet = Rule;
          // A proof that no execution reaches the end says nothing. Under BMC
          // the program is unrolled to the bound that was proved complete. A
          // pending verdict is marked once certification makes it a proof.
          if (Rule || (Pending && !Opts.LeanCertify))
            return;
          auto markVacuous = [&] {
            if (!Pending && !Diags[Verdict].Vacuous)
              Diags[Verdict].Message += " [vacuous]";
            Diags[Verdict].Vacuous = true;
          };
          bool WhollyVacuous = false;
          if (unreachable(PP, /*EntryOnly=*/false)) {
            WhollyVacuous = true;
            const bool AtEntry = unreachable(PP, /*EntryOnly=*/true);
            markVacuous();
            Diags[Verdict].VacuousAtEntry = AtEntry;
            Diags.push_back(
                {VerifyDiagnostic::Warning,
                 AtEntry
                     ? Fn->Name + ": the precondition is unsatisfiable, so "
                                  "every claim about it holds vacuously"
                     : Fn->Name + ": no execution reaches the end, so its "
                                  "postcondition holds vacuously; check the "
                                  "contracts it calls and its assumptions",
                 R.Location, Fn->Name});
            Diags.back().FindingOf = Verdict;
            Diags.back().FoundAtEntry = AtEntry;
          }
          if (!WhollyVacuous) {
            // A behavior that never applies has its postconditions unchecked.
            for (const auto &[Name, Assumes] : PP.BehaviorAssumes)
              if (proves(smokeProgram(PP, 0, falseGoal(), Assumes.get()))) {
                Diags.push_back(
                    {VerifyDiagnostic::Warning,
                     Fn->Name + ": behavior " + Name +
                         " never applies: its assumption contradicts the "
                         "preconditions, so its postconditions are never "
                         "checked",
                     Assumes->Loc, Fn->Name});
                Diags.back().FindingOf = Verdict;
                Diags.back().FoundAtEntry = true;
              }
            // A trusted contract that contradicts the state of a call makes
            // everything after the call hold vacuously.
            for (size_t I = 0; I < PP.Stmts.size(); ++I) {
              const PassiveStmt &Post = *PP.Stmts[I];
              if (Post.TrustedCallee.empty() || !Post.CallGuard)
                continue;
              auto unreached = [&](size_t Count) {
                return proves(smokeProgram(
                    PP, Count,
                    std::make_unique<VUnaryOpExpr>(
                        VUnaryOp::Not, cloneVExpr(Post.CallGuard.get()),
                        VType::makeBool(), Post.CallLoc)));
              };
              if (!unreached(I + Post.PostClauses) || unreached(I))
                continue;
              markVacuous();
              Diags.push_back(
                  {VerifyDiagnostic::Warning,
                   Fn->Name + ": the trusted contract of " +
                       Post.TrustedCallee +
                       " contradicts the state of this call, so everything "
                       "after it holds vacuously",
                   Post.CallLoc, Fn->Name});
              Diags.back().FindingOf = Verdict;
            }
          }
        };
        if (R.Status == VerifyStatus::Verified ||
            R.Status == VerifyStatus::Certified) {
          Diags.push_back(
              {R.Status == VerifyStatus::Verified ? VerifyDiagnostic::Verified
                                                  : VerifyDiagnostic::Certified,
               Fn->Name + backendSuffix(R), R.Location, Fn->Name, R});
          establish(/*Pending=*/false);
        } else if (R.Status == VerifyStatus::Exported) {
          Diags.push_back({VerifyDiagnostic::Exported,
                           "lean obligation: " + Fn->Name, R.Location, Fn->Name,
                           R});
          establish(/*Pending=*/true);
        } else if (R.Status == VerifyStatus::BoundedSafe) {
          AllOk = false;
          std::string Message = Fn->Name + backendSuffix(R);
          if (!R.Message.empty())
            Message += " (" + R.Message + ")";
          Diags.push_back({VerifyDiagnostic::BoundedSafe, std::move(Message),
                           R.Location, Fn->Name, R});
          // Kani's unreachable checks: safety within the bound says nothing
          // when no execution finishes within it (every one runs a loop
          // past the bound, or the assumptions contradict each other).
          if (unreachable(PP, /*EntryOnly=*/false)) {
            const size_t Verdict = Diags.size() - 1;
            Diags[Verdict].Message += " [vacuous]";
            Diags[Verdict].Vacuous = true;
            const std::string Bound =
                R.Bound ? std::to_string(*R.Bound) : std::string("the bound");
            Diags.push_back(
                {VerifyDiagnostic::Warning,
                 unreachable(PP, /*EntryOnly=*/true)
                     ? Fn->Name + ": the precondition is unsatisfiable, so "
                                  "every claim about it holds vacuously"
                     : Fn->Name + ": no execution finishes within " + Bound +
                           " loop iterations, so its bounded safety covers "
                           "no complete run; raise --unroll",
                 R.Location, Fn->Name});
          }
        } else if (R.Status == VerifyStatus::Failed) {
          AllOk = false;
          AnyFailed = true;
          if (!Fn->IsProof)
            FailedCallers.insert(Fn->Identity);
          // A fallback project shows a certified counterexample in Lean too.
          if (LeanFallbackBackend && R.Reason == VerifyReason::Counterexample) {
            FunctionRun::Refutation Pending{Diags.size(), std::nullopt,
                                            "the solver's model gives the "
                                            "goal's variables no values"};
            auto Item =
                llvm::find_if(Module.Obligations, [&](const Obligation &Item) {
                  return (Item.StableId.empty() ? Item.Id : Item.StableId) ==
                         R.ObligationId;
                });
            if (R.Assignment && Item != Module.Obligations.end())
              Pending.Lean = exportLeanRefutation(
                  Module, *Item, *R.Assignment, LeanModules.Specs, Pending.Why);
            Run.Refutations.push_back(std::move(Pending));
          }
          // The failure, and those after it --max-failures reports, each
          // with its counterexample and notes.
          auto failure = [&](const VerifyResult &Failure) {
            std::string Msg = "verification failed: " + Fn->Name;
            if (!Failure.ObligationId.empty())
              Msg += " [" + Failure.ObligationId + "]";
            if (!Failure.Message.empty())
              Msg += " (counterexample: " + Failure.Message + ")";
            Msg += backendSuffix(Failure);
            Diags.push_back({VerifyDiagnostic::Error, Msg, Failure.Location,
                             Fn->Name, Failure});
            Diags.back().Notes = failureNotes(*Fn, Failure);
          };
          failure(R);
          for (const VerifyResult &More : R.MoreFailures) {
            failure(More);
            Diags.back().Additional = true;
          }
        } else {
          const bool FallbackExported = R.Status == VerifyStatus::Unresolved &&
                                        exportLeanFallback(Module, Fn->Name, R);
          if (Opts.LeanCertify && FallbackExported) {
            establish(/*Pending=*/true);
          } else {
            AllOk = false;
            AnyFailed = true;
            if (!Fn->IsProof)
              FailedCallers.insert(Fn->Identity);
            std::string Message = Fn->Name + backendSuffix(R);
            if (!R.Message.empty())
              Message += " (" + R.Message + ")";
            Diags.push_back({VerifyDiagnostic::Unresolved, std::move(Message),
                             R.Location, Fn->Name, R});
          }
        }
      }
      DumpStream.flush();
    };
    // With --function, the executable functions run are the selected ones
    // and, round by round, those whose contracts a verdict of the run relies
    // on; specs, proof functions, and generated checks always run, since any
    // verdict may rest on their facts. Every verdict reported is then the
    // one a run of the whole file gives.
    std::vector<bool> Scheduled(Functions.size(), true);
    if (!Opts.FunctionPatterns.empty())
      for (size_t I = 0; I != Functions.size(); ++I)
        Scheduled[I] =
            Selected[I] || Functions[I]->IsSpec || Functions[I]->IsProof;
    std::map<std::string, size_t> IndexOf;
    for (size_t I = 0; I != Functions.size(); ++I)
      IndexOf.emplace(Functions[I]->Identity, I);
    std::vector<size_t> Batch;
    for (size_t I = 0; I != Functions.size(); ++I)
      if (Scheduled[I])
        Batch.push_back(I);
    while (!Batch.empty()) {
      if (Parallel) {
        TaskGroup Group(*Pool);
        for (size_t I : Batch)
          Group.async([&verifyFunction, I] { verifyFunction(I); });
        Group.wait();
      } else {
        for (size_t I : Batch)
          verifyFunction(I);
      }
      std::vector<size_t> Next;
      auto need = [&](const std::string &Identity) {
        auto It = IndexOf.find(Identity);
        if (It != IndexOf.end() && !Scheduled[It->second]) {
          Scheduled[It->second] = true;
          Next.push_back(It->second);
        }
      };
      for (size_t I : Batch) {
        for (const auto &[Index, Identity, Callees] : Runs[I].CallDependencies)
          for (const std::string &Callee : Callees)
            need(Callee);
        for (const SpecReliance &Reliance : Runs[I].ProofDependencies)
          for (const std::string &Callee : Reliance.Callees)
            need(Callee);
      }
      llvm::sort(Next);
      Batch = std::move(Next);
    }
    // A function whose verification Ctrl-C cut short is reported by one
    // line. Its verdicts stay, hidden, for what they establish: a query the
    // interrupt stopped left its verdict unresolved, and a proof found
    // before it is a proof.
    auto interrupted = [](FunctionRun &Run, const VFunction &Fn) {
      for (VerifyDiagnostic &D : Run.Diags)
        D.Hidden = true;
      Run.AllOk = false;
      Run.Confirmations.clear();
      Run.Refutations.clear();
      VerifyResult Result;
      Result.Status = VerifyStatus::Unresolved;
      Result.Reason = VerifyReason::Interrupted;
      Run.Diags.push_back({VerifyDiagnostic::Interrupted, Fn.Name, Fn.DeclLoc,
                           Fn.Name, std::move(Result)});
    };
    std::vector<FunctionRun::Confirmation> Confirmations;
    std::vector<FunctionRun::Refutation> Refutations;
    // What certification found of the refutations, or why it checked none.
    std::optional<std::map<std::string, std::string>> RefutationChecks;
    std::string RefutationsUnchecked;
    for (size_t I = 0; I != Runs.size(); ++I) {
      FunctionRun &Run = Runs[I];
      if (Run.Interrupted)
        interrupted(Run, *Functions[I]);
      const size_t Base = Diags.size();
      for (VerifyDiagnostic &D : Run.Diags) {
        if (D.FindingOf)
          *D.FindingOf += Base;
        // What a function --function leaves out reports stays, hidden, for
        // what it establishes.
        D.Hidden |= !Selected[I];
        Diags.push_back(std::move(D));
      }
      AllOk &= Run.AllOk;
      AnyFailed |= Run.AnyFailed;
      FailedCallers.insert(Run.FailedCallers.begin(), Run.FailedCallers.end());
      UndefinedSpecs.insert(Run.UndefinedSpecs.begin(),
                            Run.UndefinedSpecs.end());
      UnframedSpecs.insert(Run.UnframedSpecs.begin(), Run.UnframedSpecs.end());
      UnprovenPosts.insert(Run.UnprovenPosts.begin(), Run.UnprovenPosts.end());
      for (auto &[Index, Identity, Callees] : Run.CallDependencies)
        CallDependencies.emplace_back(Base + Index, std::move(Identity),
                                      std::move(Callees));
      for (SpecReliance &Reliance : Run.ProofDependencies) {
        Reliance.Index += Base;
        ProofDependencies.push_back(std::move(Reliance));
      }
      for (auto &[Index, Identity] : Run.InductiveLines)
        InductiveLines.emplace_back(Base + Index, std::move(Identity));
      for (FunctionRun::Confirmation &Pending : Run.Confirmations) {
        Pending.Index += Base;
        Confirmations.push_back(std::move(Pending));
      }
      for (FunctionRun::Refutation &Pending : Run.Refutations) {
        Pending.Index += Base;
        Refutations.push_back(std::move(Pending));
      }
      if (Run.ContractCheck)
        ContractChecks[Functions[I]->Identity] = Base + *Run.ContractCheck;
      if (DumpOS)
        *DumpOS << Run.Dump;
      if (Opts.ObligationOut)
        *Opts.ObligationOut << Run.Archive;
    }

    // Lean proofs are checked before what verdicts rest on is settled: a
    // certified one is a proof like a solver's, and one that fails, or that
    // certification does not check, establishes nothing.
    if (HasLeanProject) {
      std::vector<LeanProjectGoal> ExportedGoals;
      llvm::copy_if(LeanProjectGoals, std::back_inserter(ExportedGoals),
                    [](const LeanProjectGoal &Goal) { return Goal.Exported; });
      const std::set<std::string> *RunGroups =
          LeanFallbackBackend ? &LeanRunGroups : nullptr;
      std::vector<LeanRefutation> LeanRefutations;
      for (const FunctionRun::Refutation &Pending : Refutations)
        if (Pending.Lean)
          LeanRefutations.push_back(*Pending.Lean);
      llvm::Error Finalized = Lean->writeLeanProjectModules(LeanModules);
      if (!Finalized)
        Finalized = Lean->finalizeLeanProject(LeanProjectGoals, RunGroups);
      if (!Finalized && LeanFallbackBackend)
        Finalized = Lean->writeLeanRefutations(LeanRefutations);
      if (!Finalized && Opts.LeanAuto)
        Lean->automateLeanProject(LeanProjectGoals);
      reportLeanWarnings();
      if (!Finalized) {
        // Each export's count of the goals cppverify_auto proves.
        const std::set<std::string> Automatic =
            Lean->automaticLeanGoals(LeanProjectGoals);
        for (VerifyDiagnostic &Diagnostic : Diags)
          if (Diagnostic.K == VerifyDiagnostic::Exported && Diagnostic.Result)
            Diagnostic.LeanAutomatic = llvm::count_if(
                std::set<std::string>(Diagnostic.Result->LeanGoals.begin(),
                                      Diagnostic.Result->LeanGoals.end()),
                [&](const std::string &Goal) { return Automatic.count(Goal); });
      }
      if (Finalized) {
        AllOk = false;
        AnyFailed = true;
        Diags.push_back({VerifyDiagnostic::Error,
                         "cannot finalize Lean project (" +
                             llvm::toString(std::move(Finalized)) + ")"});
      } else if (Opts.LeanCertify && !interruptRequested() &&
                 (!ExportedGoals.empty() || !Refutations.empty() ||
                  Opts.LeanFallbackProjectPath.empty())) {
        // A verdict certification does not make a proof is reported, and
        // what its vacuity checks found is not.
        auto unproved = [&](size_t Index) {
          VerifyDiagnostic &Diagnostic = Diags[Index];
          AllOk = false;
          Diagnostic.K = VerifyDiagnostic::Unresolved;
          Diagnostic.Vacuous = false;
          for (VerifyDiagnostic &Finding : Diags)
            if (Finding.FindingOf == Index)
              Finding.Hidden = true;
        };
        auto failed = [&](size_t Index, const std::string &Reason) {
          AllOk = false;
          AnyFailed = true;
          VerifyDiagnostic &Diagnostic = Diags[Index];
          unproved(Index);
          Diagnostic.Message += " (Lean certification failed: " + Reason + ")";
          if (Diagnostic.Result) {
            Diagnostic.Result->Status = VerifyStatus::Unresolved;
            Diagnostic.Result->Reason = VerifyReason::LeanExportFailure;
            Diagnostic.Result->Message = Reason;
          }
        };
        // The goals that failed, by name, once; testing an Expected that
        // holds an error again would leave it unchecked.
        std::optional<std::map<std::string, std::string>> Certified;
        std::string NotCertified;
        if (auto Checked =
                Lean->certifyLeanProject(ExportedGoals, LeanRefutations))
          Certified = std::move(*Checked);
        else
          NotCertified = llvm::toString(Checked.takeError());
        std::map<std::string, const LeanProjectGoal *> GoalsByName;
        for (const LeanProjectGoal &Goal : ExportedGoals)
          GoalsByName.emplace(Goal.Name, &Goal);
        if (!Certified) {
          for (size_t Index = 0; Index != Diags.size(); ++Index)
            if (Diags[Index].K == VerifyDiagnostic::Exported)
              failed(Index, NotCertified);
        } else {
          for (size_t Index = 0; Index != Diags.size(); ++Index) {
            VerifyDiagnostic &Diagnostic = Diags[Index];
            if (Diagnostic.K != VerifyDiagnostic::Exported)
              continue;
            // Each goal of the function is certified, or it is not.
            std::string Reason;
            if (Diagnostic.Result)
              for (const std::string &Goal : Diagnostic.Result->LeanGoals)
                if (auto Failure = Certified->find(Goal);
                    Failure != Certified->end()) {
                  auto Known = GoalsByName.find(Goal);
                  Reason +=
                      (Reason.empty() ? "" : "; ") +
                      std::string("the proof of ") +
                      (Known != GoalsByName.end() ? Known->second->StableId
                                                  : Goal) +
                      ": " + Failure->second;
                }
            if (!Reason.empty()) {
              failed(Index, Reason);
              continue;
            }
            const ProofEvidence *Evidence =
                Diagnostic.Result && Diagnostic.Result->Evidence
                    ? &*Diagnostic.Result->Evidence
                    : nullptr;
            if (Evidence &&
                Evidence->LeanObligations.size() < Evidence->Total) {
              // Only a complete split of the obligations is a proof.
              if (!Evidence->SolverProved ||
                  *Evidence->SolverProved + Evidence->LeanObligations.size() !=
                      Evidence->Total) {
                unproved(Index);
                Diagnostic.Message += " (inconsistent proof evidence)";
                Diagnostic.Result->Status = VerifyStatus::Unresolved;
                Diagnostic.Result->Reason = VerifyReason::InvalidBackendResult;
                continue;
              }
              Diagnostic.K = VerifyDiagnostic::MixedProof;
              Diagnostic.Message = Diagnostic.FunctionName +
                                   evidenceSuffix(*Evidence, "certified");
              Diagnostic.Result->Status = VerifyStatus::MixedProof;
              Diagnostic.Result->BackendName = Evidence->Solver + "+lean";
              Diagnostic.Result->Reason = VerifyReason::None;
            } else {
              Diagnostic.K = VerifyDiagnostic::Certified;
              llvm::StringRef Name = Diagnostic.Message;
              if (!Name.consume_front("lean obligation: ")) {
                Name.consume_front("lean fallback: ");
                Name = Name.substr(0, Name.find(" ["));
              }
              Diagnostic.Message = Name.str() + " [backend=Lean]";
              if (Diagnostic.Result) {
                Diagnostic.Result->Status = VerifyStatus::Certified;
                Diagnostic.Result->BackendName = "lean";
                Diagnostic.Result->Reason = VerifyReason::None;
              }
            }
            if (Diagnostic.Vacuous)
              Diagnostic.Message += " [vacuous]";
          }
        }

        if (Certified)
          RefutationChecks = *Certified;
        else
          RefutationsUnchecked = NotCertified;
      }
    }
    for (const SpecReliance &Check : ProofDependencies)
      if (!Check.Establishes.empty() &&
          (Diags[Check.Index].K == VerifyDiagnostic::Certified ||
           Diags[Check.Index].K == VerifyDiagnostic::MixedProof)) {
        if (Check.Facts & DefinitionFact)
          UndefinedSpecs.erase(Check.Establishes);
        if (Check.Facts & ReadsFact)
          UnframedSpecs.erase(Check.Establishes);
        if (Check.Facts & PostFact)
          UnprovenPosts.erase(Check.Establishes);
      }

    // Total correctness needs every loop to terminate. A bounded proof
    // proves its unwinding, so every loop there exits within the bound.
    for (const auto &[Index, Identity, Callees] : CallDependencies) {
      VerifyDiagnostic &Diagnostic = Diags[Index];
      auto It = FnMap.find(Identity);
      if (It == FnMap.end() || It->second->UnmeasuredLoop.isInvalid() ||
          !Diagnostic.isProof() ||
          (Diagnostic.Result && Diagnostic.Result->Bound))
        continue;
      AllOk = false;
      const SourceLocation Loop = It->second->UnmeasuredLoop;
      const PresumedLoc Where = Ctx.getSourceManager().getPresumedLoc(Loop);
      Diagnostic.K = VerifyDiagnostic::Unresolved;
      Diagnostic.Loc = Loop;
      Diagnostic.Message +=
          " [reason=decreases.missing] (the loop at " +
          (Where.isValid() ? std::to_string(Where.getLine()) + ":" +
                                 std::to_string(Where.getColumn())
                           : std::string("?")) +
          " has no decreases clause: give it a measure, or "
          "cppverify::decreases(*) to allow it to diverge)";
      if (Diagnostic.Result) {
        Diagnostic.Result->Status = VerifyStatus::Unresolved;
        Diagnostic.Result->Reason = VerifyReason::DecreasesMissing;
      }
    }

    // Settle what each verdict rests on until nothing changes: the facts of
    // specs (definitions, frames, postconditions, unfoldings) and callee
    // contracts. A demoted check of a spec no longer establishes its facts,
    // a demoted function no longer its contract, and an inductive predicate
    // whose rule proofs are not all established has no unfolding.
    std::set<std::string> Unestablished;
    for (const auto &Fn : Functions)
      if (!Fn->IsSpec && !Fn->Uninterpreted && !Fn->IsTrusted)
        Unestablished.insert(Fn->Identity);
    auto settled = [&](size_t Index) { return Diags[Index].isProof(); };
    for (const auto &[Index, Identity, Callees] : CallDependencies)
      if (settled(Index))
        Unestablished.erase(Identity);
    // A contract that may be undefined establishes nothing.
    for (const auto &[Identity, Index] : ContractChecks)
      if (!settled(Index))
        Unestablished.insert(Identity);
    std::map<size_t, std::string> VerdictOf;
    for (const auto &[Index, Identity, Callees] : CallDependencies)
      VerdictOf[Index] = Identity;
    for (const auto &[Identity, Index] : ContractChecks)
      VerdictOf[Index] = Identity;
    std::map<size_t, const SpecReliance *> CheckOf;
    for (const SpecReliance &Reliance : ProofDependencies)
      if (!Reliance.Establishes.empty())
        CheckOf[Reliance.Index] = &Reliance;
    auto demote = [&](size_t Index, VerifyReason Reason,
                      const std::string &Why) {
      VerifyDiagnostic &Diagnostic = Diags[Index];
      AllOk = false;
      Diagnostic.K = VerifyDiagnostic::Unresolved;
      // A vacuity finding rests on the facts of its query. No callee
      // contract enters the entry state, but a spec fact may enter any query.
      const bool EntryStands = Reason == VerifyReason::CalleeContract;
      for (VerifyDiagnostic &Finding : Diags)
        if (Finding.FindingOf == Index &&
            !(Finding.FoundAtEntry && EntryStands))
          Finding.Hidden = true;
      if (Diagnostic.Vacuous && !(Diagnostic.VacuousAtEntry && EntryStands)) {
        Diagnostic.Vacuous = false;
        if (size_t At = Diagnostic.Message.find(" [vacuous]");
            At != std::string::npos)
          Diagnostic.Message.erase(At, std::strlen(" [vacuous]"));
      }
      Diagnostic.Message +=
          " [reason=" + verifyReasonCode(Reason).str() + "] (" + Why + ")";
      // A line with no result of its own, as an inductive predicate's, gets
      // one: the summary counts it and JSON gives its reason.
      if (!Diagnostic.Result)
        Diagnostic.Result.emplace();
      Diagnostic.Result->Status = VerifyStatus::Unresolved;
      Diagnostic.Result->Reason = Reason;
      if (auto It = CheckOf.find(Index); It != CheckOf.end()) {
        const SpecReliance &Check = *It->second;
        if (Check.Facts & DefinitionFact)
          UndefinedSpecs.insert(Check.Establishes);
        if (Check.Facts & ReadsFact)
          UnframedSpecs.insert(Check.Establishes);
        if (Check.Facts & PostFact)
          UnprovenPosts.insert(Check.Establishes);
      }
      if (auto It = VerdictOf.find(Index); It != VerdictOf.end())
        Unestablished.insert(It->second);
    };
    auto nameOf = [&](const std::string &Identity) {
      auto It = FnMap.find(Identity);
      return It != FnMap.end() ? It->second->Name : Identity;
    };
    auto list = [](std::string &List, const std::string &Name) {
      List += (List.empty() ? "" : ", ") + Name;
    };
    auto missingContracts = [&](const std::string &Self,
                                const std::set<std::string> &Callees) {
      std::string Names;
      for (const std::string &Callee : Callees)
        if (Callee != Self && Unestablished.count(Callee)) {
          list(Names, nameOf(Callee));
          auto It = FnMap.find(Callee);
          auto Check = ContractChecks.find(Callee);
          if (Check != ContractChecks.end() && !settled(Check->second))
            Names += " (its clauses are not shown to be defined)";
          else if (It != FnMap.end() && It->second->UnsupportedConstruct)
            Names += " (it uses a construct the verifier does not support)";
          else if (It != FnMap.end() && It->second->IsExternalContract &&
                   !It->second->IsTrusted)
            Names += " (no definition; mark it [[cppverify::trusted]] to "
                     "assume it)";
        }
      return Names;
    };
    std::map<std::string, std::vector<const VFunction *>> RulesOf;
    for (const auto &Fn : Functions)
      if (!Fn->InductiveRuleOf.empty())
        RulesOf[Fn->InductiveRuleOf].push_back(Fn.get());
    auto unprovedRules = [&] {
      std::map<std::string, std::string> Unproved;
      for (const auto &[Predicate, Rules] : RulesOf)
        for (const VFunction *Rule : Rules)
          if (Unestablished.count(Rule->Identity)) {
            const size_t Open = Rule->Name.rfind(" (");
            list(Unproved[Predicate],
                 Open == std::string::npos
                     ? Rule->Name
                     : Rule->Name.substr(Open + 2,
                                         Rule->Name.size() - Open - 3));
          }
      return Unproved;
    };
    for (bool Demoted = true; Demoted;) {
      for (bool Changed = true; Changed;) {
        Changed = false;
        const std::map<std::string, std::string> Unproved = unprovedRules();
        for (const SpecReliance &Reliance : ProofDependencies) {
          if (!settled(Reliance.Index))
            continue;
          // Definitions and frames of what the proof may reach;
          // postconditions and unfoldings where its module assumes them.
          std::string Unsupported, Undefined, Unframed, Unproven, Unruled;
          for (const std::string &Identity : Reliance.Specs) {
            if (auto It = FnMap.find(Identity);
                It != FnMap.end() && It->second->UnsupportedConstruct)
              list(Unsupported, nameOf(Identity));
            else if (UndefinedSpecs.count(Identity))
              list(Undefined, nameOf(Identity));
            else if (UnframedSpecs.count(Identity))
              list(Unframed, nameOf(Identity));
          }
          for (const std::set<std::string> *Posts :
               {&Reliance.AssumedPosts, &Reliance.InductivePosts})
            for (const std::string &Identity : *Posts)
              if (UnprovenPosts.count(Identity) &&
                  Identity != Reliance.Establishes &&
                  !Reliance.Withheld.count(Identity) &&
                  !Reliance.PostsWithheld.count(Identity) &&
                  Unproven.find(nameOf(Identity)) == std::string::npos)
                list(Unproven, nameOf(Identity));
          for (const std::string &Identity : Reliance.AssumedUnfoldings)
            if (Unproved.count(Identity) && !Reliance.Withheld.count(Identity))
              list(Unruled, nameOf(Identity));
          if (!Unsupported.empty())
            demote(Reliance.Index, VerifyReason::UnsupportedConstruct,
                   "relies on " + Unsupported +
                       ", which uses a construct the verifier does not "
                       "support");
          else if (!Undefined.empty())
            demote(Reliance.Index, VerifyReason::SpecTermination,
                   "relies on the definition of " + Undefined +
                       ", whose termination is not established");
          else if (!Unframed.empty())
            demote(Reliance.Index, VerifyReason::SpecReads,
                   "relies on the reads clause of " + Unframed +
                       ", which is not established");
          else if (!Unproven.empty())
            demote(Reliance.Index, VerifyReason::SpecPost,
                   "relies on the postcondition of " + Unproven +
                       ", which is not established");
          else if (!Unruled.empty())
            demote(Reliance.Index, VerifyReason::SpecInductive,
                   "relies on the unfolding of " + Unruled +
                       ", whose rules are not established");
          else if (std::string Missing = missingContracts("", Reliance.Callees);
                   !Missing.empty())
            demote(Reliance.Index, VerifyReason::CalleeContract,
                   "relies on the contract of " + Missing +
                       ", which is not established");
          else
            continue;
          Changed = true;
        }
        for (const auto &[Index, Identity, Callees] : CallDependencies) {
          if (!settled(Index))
            continue;
          std::string Missing = missingContracts(Identity, Callees);
          if (Missing.empty())
            continue;
          demote(Index, VerifyReason::CalleeContract,
                 "relies on the contract of " + Missing +
                     ", which is not established");
          Changed = true;
        }
        for (const auto &[Index, Identity] : InductiveLines)
          if (auto It = Unproved.find(Identity);
              It != Unproved.end() &&
              Diags[Index].K == VerifyDiagnostic::Verified)
            demote(Index, VerifyReason::SpecInductive,
                   "its rules are not established: " + It->second);
        // A counterexample whose check needed a postcondition rests on it.
        for (size_t Index = 0; Index != Diags.size(); ++Index) {
          VerifyDiagnostic &Diagnostic = Diags[Index];
          if (Diagnostic.K != VerifyDiagnostic::Error || !Diagnostic.Result ||
              Diagnostic.Result->CertifiedWith.empty())
            continue;
          std::string Undefined, Unruled, Unproven;
          for (const std::string &Identity : Diagnostic.Result->CertifiedWith)
            if (UndefinedSpecs.count(Identity))
              list(Undefined, nameOf(Identity));
            else if (Unproved.count(Identity))
              list(Unruled, nameOf(Identity));
            else if (UnprovenPosts.count(Identity))
              list(Unproven, nameOf(Identity));
          if (Undefined.empty() && Unruled.empty() && Unproven.empty())
            continue;
          std::string &Message = Diagnostic.Message;
          if (size_t At = Message.find(" [reason=counterexample]");
              At != std::string::npos)
            Message.erase(At, std::string(" [reason=counterexample]").size());
          if (size_t At = Message.find("failed"); At != std::string::npos)
            Message.replace(At, 6, "unresolved");
          if (!Undefined.empty())
            demote(Index, VerifyReason::SpecTermination,
                   "its counterexample rests on the definition of " +
                       Undefined + ", whose termination is not established");
          else if (!Unruled.empty())
            demote(Index, VerifyReason::SpecInductive,
                   "its counterexample rests on the unfolding of " + Unruled +
                       ", whose rules are not established");
          else
            demote(Index, VerifyReason::SpecPost,
                   "its counterexample is checked with the postcondition of " +
                       Unproven + ", which is not established");
          Changed = true;
        }
      }

      // No proof may rest on itself. A fact is established only by verdicts
      // whose own dependencies are, starting from none (a least fixpoint);
      // recursion is justified only through a checked measure: within a
      // function's recursion cycle, and by a spec's induction hypothesis.
      Demoted = false;
      auto fact = [](char Kind, const std::string &Identity) {
        return std::string(1, Kind) + Identity;
      };
      std::map<std::string, std::vector<size_t>> Producers;
      std::set<size_t> Verdicts;
      // A contract is established by its function's proof and by the
      // check that it is defined.
      for (const auto &[Identity, Index] : ContractChecks) {
        Verdicts.insert(Index);
        Producers[fact('C', Identity)].push_back(Index);
      }
      for (const auto &[Index, Identity, Callees] : CallDependencies) {
        Verdicts.insert(Index);
        Producers[fact('C', Identity)].push_back(Index);
        auto It = FnMap.find(Identity);
        if (It != FnMap.end() && !It->second->InductiveRuleOf.empty())
          Producers[fact('U', It->second->InductiveRuleOf)].push_back(Index);
      }
      for (const SpecReliance &Reliance : ProofDependencies) {
        Verdicts.insert(Reliance.Index);
        if (Reliance.Establishes.empty())
          continue;
        if (Reliance.Facts & DefinitionFact)
          Producers[fact('D', Reliance.Establishes)].push_back(Reliance.Index);
        if (Reliance.Facts & PostFact)
          Producers[fact('P', Reliance.Establishes)].push_back(Reliance.Index);
        if (Reliance.Facts & ReadsFact)
          Producers[fact('R', Reliance.Establishes)].push_back(Reliance.Index);
      }
      auto cycleOf = [&](const std::string &Identity) {
        std::set<std::string> Cycle;
        if (auto It = FnMap.find(Identity); It != FnMap.end())
          Cycle = It->second->RecursionGroup;
        Cycle.insert(Identity);
        return Cycle;
      };
      // A cluster's members use each other's contracts, postconditions, and
      // definitions only below their shared measure, so their proofs rest
      // on each other by well-founded induction; frames are not so guarded.
      auto clusterOf = [&](const std::string &Identity) {
        std::set<std::string> Cluster = cycleOf(Identity);
        if (auto It = FnMap.find(Identity); It != FnMap.end())
          Cluster.insert(It->second->Cluster.begin(),
                         It->second->Cluster.end());
        return Cluster;
      };
      std::map<size_t, std::set<std::string>> Needs;
      for (const auto &[Index, Identity, Callees] : CallDependencies) {
        const std::set<std::string> Cluster = clusterOf(Identity);
        for (const std::string &Callee : Callees)
          if (!Cluster.count(Callee))
            Needs[Index].insert(fact('C', Callee));
      }
      for (const SpecReliance &Reliance : ProofDependencies) {
        std::set<std::string> &Mine = Needs[Reliance.Index];
        const std::string Self =
            !Reliance.Establishes.empty()     ? Reliance.Establishes
            : VerdictOf.count(Reliance.Index) ? VerdictOf[Reliance.Index]
                                              : std::string();
        const std::set<std::string> Cycle =
            Self.empty() ? std::set<std::string>() : cycleOf(Self);
        const std::set<std::string> Cluster =
            Self.empty() ? std::set<std::string>() : clusterOf(Self);
        for (const std::string &Callee : Reliance.Callees)
          if (!Cluster.count(Callee))
            Mine.insert(fact('C', Callee));
        // Definitions and frames of what the proof mentions; postconditions
        // and unfoldings only where it assumes them.
        for (const std::string &Spec : Reliance.Specs) {
          if (Spec == Reliance.Establishes) {
            if (!(Reliance.Facts & DefinitionFact))
              Mine.insert(fact('D', Spec));
            continue;
          }
          if (!Cluster.count(Spec))
            Mine.insert(fact('D', Spec));
          if (!Cycle.count(Spec))
            Mine.insert(fact('R', Spec));
        }
        for (const std::string &Spec : Reliance.AssumedPosts)
          if (Spec != Reliance.Establishes && !Cycle.count(Spec) &&
              !Reliance.Withheld.count(Spec))
            Mine.insert(fact('P', Spec));
        for (const std::string &Spec : Reliance.AssumedUnfoldings)
          if (!Cycle.count(Spec) && !Reliance.Withheld.count(Spec))
            Mine.insert(fact('U', Spec));
      }
      std::set<std::string> Established;
      std::set<size_t> Sound;
      auto established = [&](const std::string &Fact) {
        return !Producers.count(Fact) || Established.count(Fact);
      };
      for (bool Changed = true; Changed;) {
        Changed = false;
        for (size_t Index : Verdicts)
          if (!Sound.count(Index) && settled(Index) &&
              llvm::all_of(Needs[Index], established)) {
            Sound.insert(Index);
            Changed = true;
          }
        for (const auto &[Fact, Indices] : Producers)
          if (!Established.count(Fact) &&
              llvm::all_of(Indices,
                           [&](size_t Index) { return Sound.count(Index); })) {
            Established.insert(Fact);
            Changed = true;
          }
      }
      auto describe = [&](const std::string &Fact) {
        const std::string Name = nameOf(Fact.substr(1));
        switch (Fact[0]) {
        case 'C':
          return "the contract of " + Name;
        case 'D':
          return "the definition of " + Name;
        case 'P':
          return "the postcondition of " + Name;
        case 'R':
          return "the reads clause of " + Name;
        default:
          return "the rules of " + Name;
        }
      };
      for (size_t Index : Verdicts) {
        if (Sound.count(Index) || !settled(Index))
          continue;
        std::string Names;
        for (const std::string &Fact : Needs[Index])
          if (!established(Fact))
            list(Names, describe(Fact));
        demote(Index, VerifyReason::ProofCycle,
               "relies on " + Names +
                   ", whose proof rests in turn on this one; proofs rest on "
                   "each other only by induction, when the functions share "
                   "decreases clauses of one length that every call and "
                   "application between them lowers");
        Demoted = true;
      }
      for (const auto &[Index, Identity] : InductiveLines)
        if (!established(fact('U', Identity)) &&
            Diags[Index].K == VerifyDiagnostic::Verified) {
          demote(Index, VerifyReason::ProofCycle,
                 "its rules rest on facts whose proofs rest on them");
          Demoted = true;
        }
    }
    // Counterexamples their checks could not evaluate are confirmed by proof
    // now that it is known which contracts are established: a confirmation
    // rests only on those, and only where the spec facts its query assumes
    // are established. Turning an unresolved verdict into a failure changes
    // no other verdict, since neither establishes a contract.
    if (!Confirmations.empty()) {
      const std::map<std::string, std::string> UnprovedRules = unprovedRules();
      std::map<std::string, std::shared_ptr<const ContractTheorem>> Lemmas;
      for (size_t I = 0; I != Functions.size(); ++I)
        if (Runs[I].Contract && !Unestablished.count(Functions[I]->Identity))
          Lemmas.emplace(Functions[I]->Identity, Runs[I].Contract);
      std::vector<std::optional<VerifyResult>> Outcomes(Confirmations.size());
      std::vector<char> CutShort(Confirmations.size());
      auto confirm = [&](size_t I) {
        NodeBudget::Limit NodeLimit(Opts.MaxQueryNodes);
        const FunctionRun::Confirmation &Pending = Confirmations[I];
        const VerifyDiagnostic &Verdict = Diags[Pending.Index];
        if (Verdict.K != VerifyDiagnostic::Unresolved ||
            Verdict.FunctionName != Pending.Fn->Name)
          return;
        const ObligationModule &Checked = *Pending.Module;
        for (const std::string &Identity : Checked.AssumedPosts)
          if (UnprovenPosts.count(Identity))
            return;
        for (const std::string &Identity : Checked.AssumedUnfoldings)
          if (UnprovedRules.count(Identity))
            return;
        for (const auto &[Identity, Function] : Checked.LogicFunctions) {
          (void)Function;
          if (UndefinedSpecs.count(Identity))
            return;
        }
        if (interruptRequested()) {
          CutShort[I] = true;
          return;
        }
        std::unique_ptr<VerifyBackend> By = createVerifyBackend(
            Pending.Kind, nullptr, Opts.BMCUnroll, Execution, nullptr);
        Outcomes[I] = confirmCounterexample(
            Checked, Pending.Result, InterfaceMap, *Pending.Fn, Lemmas, *By);
        CutShort[I] = !Outcomes[I] && interruptRequested();
      };
      if (Parallel) {
        TaskGroup Group(*Pool);
        for (size_t I = 0; I != Confirmations.size(); ++I)
          Group.async([&confirm, I] { confirm(I); });
        Group.wait();
      } else {
        for (size_t I = 0; I != Confirmations.size(); ++I)
          confirm(I);
      }
      for (size_t I = 0; I != Confirmations.size(); ++I) {
        if (CutShort[I]) {
          VerifyDiagnostic &Verdict = Diags[Confirmations[I].Index];
          Verdict.K = VerifyDiagnostic::Interrupted;
          Verdict.Message = Confirmations[I].Fn->Name;
          if (Verdict.Result)
            Verdict.Result->Reason = VerifyReason::Interrupted;
          continue;
        }
        if (!Outcomes[I])
          continue;
        const FunctionRun::Confirmation &Pending = Confirmations[I];
        VerifyDiagnostic &Verdict = Diags[Pending.Index];
        VerifyResult &Failed = *Outcomes[I];
        std::string Message;
        if (Pending.Label == "verification") {
          Message = "verification failed: " + Pending.Fn->Name;
          if (!Failed.ObligationId.empty())
            Message += " [" + Failed.ObligationId + "]";
          Message += " (counterexample: " + Failed.Message + ")" +
                     backendSuffix(Failed);
        } else {
          Message = Pending.Label + " failed: " + Pending.Fn->Name +
                    backendSuffix(Failed) + " (" + Failed.Message + ")";
        }
        std::string Trusted;
        for (const std::string &Identity : Failed.ConfirmedWithContracts)
          if (auto It = FnMap.find(Identity); It != FnMap.end()) {
            Verdict.ConfirmedWith.push_back(It->second->Name);
            if (It->second->IsTrusted) {
              Trusted += (Trusted.empty() ? "" : ",") + It->second->Name;
              Verdict.Trusts.push_back(It->second->Name);
            }
          }
        if (!Trusted.empty())
          Message += " [trusts=" + Trusted + "]";
        Verdict.K = VerifyDiagnostic::Error;
        Verdict.Message = std::move(Message);
        Verdict.Result = std::move(Failed);
        AllOk = false;
        AnyFailed = true;
      }
    }
    // A proof trusts what its callees' proofs trust, too.
    std::map<std::string, std::set<std::string>> Trusts;
    for (bool Changed = true; Changed;) {
      Changed = false;
      for (const auto &[Index, Identity, Callees] : CallDependencies) {
        std::set<std::string> &Mine = Trusts[Identity];
        const size_t Before = Mine.size();
        for (const std::string &Callee : Callees) {
          auto It = FnMap.find(Callee);
          if (It == FnMap.end() || Callee == Identity)
            continue;
          if (It->second->IsTrusted)
            Mine.insert(It->second->Name);
          if (auto Inherited = Trusts.find(Callee); Inherited != Trusts.end())
            Mine.insert(Inherited->second.begin(), Inherited->second.end());
        }
        Changed |= Mine.size() != Before;
      }
    }
    for (const auto &[Index, Identity, Callees] : CallDependencies) {
      VerifyDiagnostic &Diagnostic = Diags[Index];
      if (!Diagnostic.isProof())
        continue;
      std::string Trusted;
      for (const std::string &Name : Trusts[Identity]) {
        Trusted += (Trusted.empty() ? "" : ",") + Name;
        Diagnostic.Trusts.push_back(Name);
      }
      if (!Trusted.empty())
        Diagnostic.Message += " [trusts=" + Trusted + "]";
    }
    // A certified failure stands on the certifier's evaluation. Its
    // refutation shows it in Lean too; one Lean decides the other way is a
    // disagreement between two evaluators of one goal, never a failure. Only
    // the failures that stand once the verdicts settle are reported.
    for (const FunctionRun::Refutation &Pending : Refutations) {
      if ((!RefutationChecks && RefutationsUnchecked.empty()) ||
          Diags[Pending.Index].K != VerifyDiagnostic::Error)
        continue;
      const std::string Function = Diags[Pending.Index].FunctionName;
      std::string Why = Pending.Why;
      if (Pending.Lean && !RefutationChecks) {
        Why = RefutationsUnchecked;
      } else if (Pending.Lean) {
        auto Outcome = RefutationChecks->find(Pending.Lean->Goal + "_refuted");
        if (Outcome == RefutationChecks->end()) {
          Diags[Pending.Index].Message += " (confirmed in Lean)";
          Diags[Pending.Index].LeanRefuted = true;
          continue;
        }
        Why = Outcome->second;
        if (llvm::StringRef(Why).contains(
                "Lean decides the goal true at the counterexample")) {
          VerifyDiagnostic &Failure = Diags[Pending.Index];
          const std::string Detail =
              "Lean decides the goal of " + Pending.Lean->StableId +
              " true at the solver's counterexample, which the certifier "
              "found false";
          Failure.K = VerifyDiagnostic::Unresolved;
          Failure.Message = Function + " (" + Detail + ")";
          if (Failure.Result) {
            Failure.Result->Status = VerifyStatus::Unresolved;
            Failure.Result->Reason = VerifyReason::InconsistentBackendResults;
            Failure.Result->Message = Detail;
            Failure.Message += backendSuffix(*Failure.Result);
          }
          continue;
        }
      }
      // What the refutation tactic says, else the first line.
      llvm::StringRef Said = Why;
      if (size_t At = Said.find("cppverify: "); At != llvm::StringRef::npos)
        Said = Said.substr(At + std::strlen("cppverify: "));
      Said = Said.take_until([](char C) { return C == '\n'; });
      Diags.push_back({VerifyDiagnostic::Warning,
                       "the counterexample of " + Function +
                           " is not confirmed in Lean: " + Said.str()});
    }

    // Calls from code that is not verified rely on the precondition without
    // checking it, so the proof holds only where they establish it.
    for (const auto &[Index, Identity, Callees] : CallDependencies) {
      VerifyDiagnostic &Diagnostic = Diags[Index];
      auto Callers = UnverifiedCallers.find(Identity);
      auto Fn = FnMap.find(Identity);
      if (Callers == UnverifiedCallers.end() || Fn == FnMap.end() ||
          llvm::none_of(
              Fn->second->Preconditions,
              [](const std::unique_ptr<VExpr> &Pre) {
                return Pre->K != VExpr::Literal ||
                       static_cast<const VLiteralExpr &>(*Pre).Value != "1";
              }) ||
          !Diagnostic.isProof())
        continue;
      std::string Names;
      for (const std::string &Name : Callers->second) {
        Names += (Names.empty() ? "" : ", ") + Name;
        Diagnostic.UnverifiedCallers.push_back(Name);
      }
      Diagnostic.Message += " (its precondition is assumed, not checked, at "
                            "calls from unverified " +
                            Names + ")";
    }

    // decreases(*) allows divergence, and so does calling a function that
    // may diverge: such a proof covers only the executions that terminate.
    std::map<std::string, std::string> Diverges;
    for (const auto &Fn : Functions)
      if (Fn->DivergenceLoc.isValid()) {
        const PresumedLoc Where =
            Ctx.getSourceManager().getPresumedLoc(Fn->DivergenceLoc);
        Diverges[Fn->Identity] =
            "cppverify::decreases(*) at " +
            (Where.isValid() ? std::to_string(Where.getLine()) + ":" +
                                   std::to_string(Where.getColumn())
                             : std::string("?")) +
            " allows it to diverge";
      }
    for (bool Changed = true; Changed;) {
      Changed = false;
      for (const auto &Fn : Functions) {
        if (Fn->IsSpec || Fn->IsProof || Diverges.count(Fn->Identity))
          continue;
        std::set<std::string> Callees;
        collectCallees(Fn->Body, Callees);
        for (const std::string &Callee : Callees)
          if (auto It = Diverges.find(Callee); It != Diverges.end()) {
            auto Target = FnMap.find(Callee);
            Diverges[Fn->Identity] =
                "it calls " +
                (Target != FnMap.end() ? Target->second->Name : Callee) +
                ", which may diverge";
            Changed = true;
            break;
          }
      }
    }
    for (const auto &[Index, Identity, Callees] : CallDependencies) {
      VerifyDiagnostic &Diagnostic = Diags[Index];
      auto It = Diverges.find(Identity);
      if (It == Diverges.end() || !Diagnostic.isProof())
        continue;
      Diagnostic.Message += " [partial]";
      Diagnostic.Partial = true;
      Diags.push_back({VerifyDiagnostic::Warning,
                       Diagnostic.FunctionName +
                           ": proved only for executions that terminate: " +
                           It->second,
                       SourceLocation(), Diagnostic.FunctionName});
    }

    if (AnyFailed && !Opts.LowerOnly && isDeductiveBackend(Opts.Backend) &&
        !interruptRequested()) {
      BackendExecutionOptions RecommendsExecution = Execution;
      RecommendsExecution.Jobs = 1;
      RecommendsExecution.ProofCachePath.clear();
      auto Z3 =
          createVerifyBackend(BackendKind::Z3, nullptr, 0, RecommendsExecution);
      for (const auto &Fn : Functions) {
        if (!FailedCallers.count(Fn->Identity) || Fn->IsSpec || Fn->IsProof ||
            Fn->IsExternalContract)
          continue;
        checkCalleeRecommendsOnFailure(*Fn, FnMap, *Z3);
      }
    }

    // A run --function narrows succeeds when what it reports does.
    if (!Opts.FunctionPatterns.empty())
      return llvm::none_of(Diags, [](const VerifyDiagnostic &D) {
        return !D.Hidden && (D.K == VerifyDiagnostic::Error ||
                             D.K == VerifyDiagnostic::Unresolved ||
                             D.K == VerifyDiagnostic::Interrupted ||
                             D.K == VerifyDiagnostic::BoundedSafe);
      });
    return AllOk;
  }

  void printJSONDiagnostic(const VerifyDiagnostic &D,
                           llvm::raw_ostream &OS) const {
    llvm::json::Object Record;
    Record["schema"] = "cppverify.diagnostic/1";
    Record["status"] =
        D.Result ? verifyStatusCode(D.Result->Status) : diagnosticKindCode(D.K);
    Record["severity"] =
        D.K == VerifyDiagnostic::Warning || D.K == VerifyDiagnostic::BoundedSafe
            ? "warning"
        : D.K == VerifyDiagnostic::Error ||
                D.K == VerifyDiagnostic::Unresolved ||
                D.K == VerifyDiagnostic::Interrupted
            ? "error"
            : "note";
    Record["message"] = jsonText(D.Message);
    if (!D.Notes.empty()) {
      llvm::json::Array Notes;
      for (const std::string &Note : D.Notes)
        Notes.push_back(jsonText(Note));
      Record["notes"] = std::move(Notes);
    }
    if (!D.FunctionName.empty())
      Record["function"] = jsonText(D.FunctionName);

    ObligationSource Source;
    if (D.Result)
      Source = D.Result->Source;
    if (!Source.isValid() && D.Loc.isValid()) {
      PresumedLoc Location = Ctx.getSourceManager().getPresumedLoc(D.Loc);
      if (Location.isValid()) {
        Source.File = Location.getFilename();
        Source.Line = Location.getLine();
        Source.Column = Location.getColumn();
        Source.EndLine = Source.Line;
        Source.EndColumn = Source.Column;
        if (D.Span.isValid())
          if (PresumedLoc End =
                  Ctx.getSourceManager().getPresumedLoc(D.Span.getEnd());
              End.isValid()) {
            Source.EndLine = End.getLine();
            Source.EndColumn = End.getColumn();
          }
      }
    }
    if (Source.isValid())
      Record["source"] = sourceJSON(Source);
    if (const std::pair<SourceLocation, std::string> *Instantiation =
            instantiationOf(D))
      if (PresumedLoc Point =
              Ctx.getSourceManager().getPresumedLoc(Instantiation->first);
          Point.isValid()) {
        ObligationSource At;
        At.File = Point.getFilename();
        At.Line = At.EndLine = Point.getLine();
        At.Column = At.EndColumn = Point.getColumn();
        Record["instantiated_at"] = sourceJSON(At);
      }

    if (D.Vacuous)
      Record["vacuous"] = true;
    if (D.Partial)
      Record["partial"] = true;
    if (!D.Trusts.empty()) {
      llvm::json::Array Trusted;
      for (const std::string &Name : D.Trusts)
        Trusted.push_back(jsonText(Name));
      Record["trusts"] = std::move(Trusted);
    }
    if (!D.UnverifiedCallers.empty()) {
      llvm::json::Array Callers;
      for (const std::string &Name : D.UnverifiedCallers)
        Callers.push_back(jsonText(Name));
      Record["unverified_callers"] = std::move(Callers);
    }
    if (D.K == VerifyDiagnostic::Exported && D.LeanAutomatic)
      Record["lean_automatic"] = static_cast<int64_t>(D.LeanAutomatic);
    if (D.LeanRefuted)
      Record["lean_refuted"] = true;
    if (D.Result) {
      const VerifyResult &Result = *D.Result;
      if (!Result.BackendName.empty())
        Record["backend"] = Result.BackendName;
      if (Result.Reason != VerifyReason::None)
        Record["reason"] = verifyReasonCode(Result.Reason);
      if (Result.Bound)
        Record["bound"] = static_cast<int64_t>(*Result.Bound);
      if (!Result.ExploredBounds.empty()) {
        llvm::json::Array Bounds;
        for (unsigned Bound : Result.ExploredBounds)
          Bounds.push_back(static_cast<int64_t>(Bound));
        Record["explored_bounds"] = std::move(Bounds);
      }
      if (Result.ReusedQueries)
        Record["reused_queries"] = static_cast<int64_t>(Result.ReusedQueries);
      if (Result.CacheHits || Result.CacheMisses || Result.CacheErrors) {
        llvm::json::Object Cache;
        Cache["hits"] = static_cast<int64_t>(Result.CacheHits);
        Cache["misses"] = static_cast<int64_t>(Result.CacheMisses);
        Cache["errors"] = static_cast<int64_t>(Result.CacheErrors);
        Record["cache"] = std::move(Cache);
      }
      if (!Result.CacheError.empty())
        Record["cache_error"] = jsonText(Result.CacheError);
      if (!Result.InductionUsed.empty())
        Record["induction"] = jsonText(Result.InductionUsed);
      if (!Result.InductionTried.empty()) {
        llvm::json::Array Tried;
        for (const std::string &Each : Result.InductionTried)
          Tried.push_back(jsonText(Each));
        Record["induction_tried"] = std::move(Tried);
      }
      if (!Result.UncheckedApplication.empty()) {
        llvm::json::Object Unchecked;
        Unchecked["application"] = jsonText(Result.UncheckedApplication);
        llvm::json::Array Values;
        for (const VerifyModelValue &Value : Result.Unchecked) {
          llvm::json::Object Item;
          Item["name"] = jsonText(Value.DisplayName);
          Item["ssa"] = jsonText(Value.InternalName);
          Item["type"] = formatLogicSort(Value.Sort);
          Item["value"] = Value.Value
                              ? llvm::json::Value(jsonText(*Value.Value))
                              : llvm::json::Value(nullptr);
          Values.push_back(std::move(Item));
        }
        Unchecked["model"] = std::move(Values);
        Record["unchecked_counterexample"] = std::move(Unchecked);
      }
      if (!D.ConfirmedWith.empty()) {
        llvm::json::Array Contracts;
        for (const std::string &Name : D.ConfirmedWith)
          Contracts.push_back(jsonText(Name));
        Record["confirmed_with"] = std::move(Contracts);
      }
      if (!Result.QuantifierProfile.empty()) {
        llvm::json::Array Quantifiers;
        for (const QuantifierProfileEntry &Entry : Result.QuantifierProfile) {
          llvm::json::Object Item;
          Item["line"] = static_cast<int64_t>(Entry.Line);
          Item["column"] = static_cast<int64_t>(Entry.Column);
          Item["instances"] = static_cast<int64_t>(Entry.Instances);
          Item["max_generation"] = static_cast<int64_t>(Entry.MaxGeneration);
          Quantifiers.push_back(std::move(Item));
        }
        Record["quantifier_profile"] = std::move(Quantifiers);
      }
      if (Result.Evidence) {
        llvm::json::Object Evidence;
        Evidence["solver"] = Result.Evidence->Solver;
        Evidence["total"] = static_cast<int64_t>(Result.Evidence->Total);
        Evidence["solver_proved"] =
            Result.Evidence->SolverProved
                ? llvm::json::Value(
                      static_cast<int64_t>(*Result.Evidence->SolverProved))
                : llvm::json::Value(nullptr);
        llvm::json::Array Lean;
        for (const std::string &Id : Result.Evidence->LeanObligations)
          Lean.push_back(jsonText(Id));
        Evidence["lean"] = std::move(Lean);
        Record["evidence"] = std::move(Evidence);
      }
      if (!Result.ObligationId.empty()) {
        llvm::json::Object Obligation;
        Obligation["id"] = jsonText(Result.ObligationId);
        if (Result.ObligationType)
          Obligation["kind"] = obligationKindName(*Result.ObligationType);
        if (Result.Source.isValid())
          Obligation["source"] = sourceJSON(Result.Source);
        Record["obligation"] = std::move(Obligation);
      }
      if (!Result.Model.empty()) {
        llvm::json::Array Model;
        for (const VerifyModelValue &Value : Result.Model) {
          llvm::json::Object Entry;
          Entry["name"] = jsonText(Value.DisplayName);
          Entry["ssa_name"] = jsonText(Value.InternalName);
          Entry["sort"] = formatLogicSort(Value.Sort);
          Entry["value"] = Value.Value
                               ? llvm::json::Value(jsonText(*Value.Value))
                               : llvm::json::Value(nullptr);
          if (Value.Source.isValid())
            Entry["source"] = sourceJSON(Value.Source);
          Model.push_back(std::move(Entry));
        }
        Record["model"] = std::move(Model);
      }
      if (!Result.Trace.empty()) {
        llvm::json::Array Trace;
        for (const VerifyTraceEvent &Event : Result.Trace) {
          llvm::json::Object Entry;
          Entry["kind"] = traceKindCode(Event.Kind);
          Entry["message"] = jsonText(Event.Message);
          Entry["active"] = Event.Active ? llvm::json::Value(*Event.Active)
                                         : llvm::json::Value(nullptr);
          if (Event.Source.isValid())
            Entry["source"] = sourceJSON(Event.Source);
          llvm::json::Array Values;
          for (const VerifyTraceValue &Value : Event.Values) {
            llvm::json::Object Item;
            Item["label"] = jsonText(Value.Label);
            Item["sort"] = formatLogicSort(Value.Sort);
            Item["value"] = Value.Value
                                ? llvm::json::Value(jsonText(*Value.Value))
                                : llvm::json::Value(nullptr);
            Values.push_back(std::move(Item));
          }
          if (!Values.empty())
            Entry["values"] = std::move(Values);
          Trace.push_back(std::move(Entry));
        }
        Record["trace"] = std::move(Trace);
      }
    }
    OS << llvm::formatv("{0}\n", llvm::json::Value(std::move(Record)));
  }

  /// Counts the verdict D reports, if it reports one: an error reports a
  /// verdict only when it carries one, as the first error of a function the
  /// verifier does not represent does.
  static void count(const VerifyDiagnostic &D, VerifySummary &Summary) {
    if (D.Axiom || D.Additional)
      return;
    switch (D.K) {
    case VerifyDiagnostic::Verified:
    case VerifyDiagnostic::Certified:
    case VerifyDiagnostic::MixedProof:
      ++Summary.Verified;
      return;
    case VerifyDiagnostic::Error:
    case VerifyDiagnostic::Unresolved:
      if (!D.Result)
        return;
      if (D.Result->Status == VerifyStatus::Failed) {
        ++Summary.Failed;
        return;
      }
      ++Summary.Unresolved;
      ++Summary.Reasons[verifyReasonCode(D.Result->Reason).str()];
      return;
    case VerifyDiagnostic::BoundedSafe:
      ++Summary.BoundedSafe;
      return;
    case VerifyDiagnostic::Trusted:
      ++Summary.Trusted;
      return;
    case VerifyDiagnostic::Lowered:
      ++Summary.Lowered;
      return;
    case VerifyDiagnostic::Exported:
      ++Summary.Exported;
      return;
    case VerifyDiagnostic::Interrupted:
      ++Summary.Interrupted;
      return;
    case VerifyDiagnostic::Warning:
      return;
    }
  }

  void printDiagnostics(llvm::raw_ostream &OS) const {
    for (const auto &[Loc, Line] : Listing) {
      PresumedLoc PLoc = Ctx.getSourceManager().getPresumedLoc(Loc);
      if (PLoc.isValid())
        OS << PLoc.getFilename() << ":" << PLoc.getLine() << ":"
           << PLoc.getColumn() << ": ";
      OS << Line << "\n";
    }
    for (const auto &D : Diags) {
      if (D.Hidden)
        continue;
      // A generated proof is reported only if it is not a proof.
      if (D.Quiet && (D.K == VerifyDiagnostic::Verified ||
                      D.K == VerifyDiagnostic::Certified ||
                      D.K == VerifyDiagnostic::Exported))
        continue;
      if (Opts.Summary)
        count(D, *Opts.Summary);
      // --quiet leaves out what needs no attention.
      if (Opts.Quiet && (D.isProof() || D.K == VerifyDiagnostic::Lowered ||
                         D.K == VerifyDiagnostic::Exported ||
                         D.K == VerifyDiagnostic::Trusted))
        continue;
      if (Opts.Diagnostics == DiagnosticFormat::Json) {
        printJSONDiagnostic(D, OS);
        continue;
      }
      const std::pair<SourceLocation, std::string> *Instantiation =
          instantiationOf(D);
      const std::string InstantiationNote =
          Instantiation ? "in instantiation of " + Instantiation->second +
                              " '" + D.FunctionName + "' requested here"
                        : std::string();
      if (D.K == VerifyDiagnostic::Error && D.Span.isValid()) {
        DiagnosticOptions DiagOpts;
        DiagOpts.ShowPresumedLoc = true;
        TextDiagnostic Text(OS, Ctx.getLangOpts(), DiagOpts);
        Text.emitDiagnostic(
            FullSourceLoc(D.Span.getBegin(), Ctx.getSourceManager()),
            DiagnosticsEngine::Error, D.Message,
            CharSourceRange::getTokenRange(D.Span), {});
        if (Instantiation)
          Text.emitDiagnostic(
              FullSourceLoc(Instantiation->first, Ctx.getSourceManager()),
              DiagnosticsEngine::Note, InstantiationNote, {}, {});
        continue;
      }
      if (D.Loc.isValid()) {
        PresumedLoc PLoc = Ctx.getSourceManager().getPresumedLoc(D.Loc);
        if (PLoc.isValid())
          OS << PLoc.getFilename() << ":" << PLoc.getLine() << ":"
             << PLoc.getColumn() << ": ";
      }
      switch (D.K) {
      case VerifyDiagnostic::Lowered:
        OS << "Lowered: " << D.Message << "\n";
        break;
      case VerifyDiagnostic::Verified:
        OS << "Verified: " << D.Message << "\n";
        break;
      case VerifyDiagnostic::Error:
        OS << "error: " << D.Message << "\n";
        break;
      case VerifyDiagnostic::Unresolved:
        OS << "Unresolved: " << D.Message << "\n";
        if (D.Result)
          for (const QuantifierProfileEntry &Entry : D.Result->QuantifierProfile)
            OS << "note: the quantifier at " << Entry.Line << ":"
               << Entry.Column << " was instantiated " << Entry.Instances
               << " times, up to generation " << Entry.MaxGeneration << "\n";
        break;
      case VerifyDiagnostic::Interrupted:
        OS << "Interrupted: " << D.Message << "\n";
        break;
      case VerifyDiagnostic::BoundedSafe:
        OS << "BoundedSafe: " << D.Message << "\n";
        break;
      case VerifyDiagnostic::Exported:
        OS << "Exported: " << D.Message;
        if (D.LeanAutomatic && D.Result)
          OS << " (cppverify_auto proved " << D.LeanAutomatic << " of "
             << std::set<std::string>(D.Result->LeanGoals.begin(),
                                      D.Result->LeanGoals.end())
                    .size()
             << " goals)";
        OS << "\n";
        break;
      case VerifyDiagnostic::Certified:
        OS << "Certified: " << D.Message << "\n";
        break;
      case VerifyDiagnostic::MixedProof:
        OS << "Proved (" << D.Result->BackendName << "): " << D.Message << "\n";
        break;
      case VerifyDiagnostic::Trusted:
        OS << "Trusted: " << D.Message << "\n";
        break;
      case VerifyDiagnostic::Warning:
        OS << "warning: " << D.Message << "\n";
        break;
      }
      if (Instantiation) {
        PresumedLoc PLoc =
            Ctx.getSourceManager().getPresumedLoc(Instantiation->first);
        if (PLoc.isValid())
          OS << PLoc.getFilename() << ":" << PLoc.getLine() << ":"
             << PLoc.getColumn() << ": ";
        OS << "note: " << InstantiationNote << "\n";
      }
      for (const std::string &Note : D.Notes)
        OS << "note: " << Note << "\n";
    }
  }
};

} // namespace

bool verify::verifyTranslationUnit(ASTContext &Ctx, llvm::raw_ostream &OS,
                                   const VerifyOptions &Opts) {
  Verifier V(Ctx, Opts, OS);
  bool Ok = V.run();
  V.printDiagnostics(OS);
  return Ok;
}

LeanProjectReplay
verify::replayLeanProject(const std::vector<ObligationModule> &Modules,
                          const VerifyOptions &Opts) {
  LeanProjectReplay Replay;
  LeanProject Project(Opts);
  auto report = [&] {
    for (std::string &Warning : Project.takeWarnings())
      Replay.Warnings.push_back(std::move(Warning));
  };
  llvm::Error Error = Project.initializeLeanProject();
  report();
  if (Error) {
    Replay.Error = "cannot initialize Lean project (" +
                   llvm::toString(std::move(Error)) + ")";
    return Replay;
  }

  // The goals have the names, files, and proofs a source run gives the
  // same obligations, since both name them by their statements.
  std::vector<LeanProjectGoal> Goals;
  LeanProjectModules Generated;
  LeanVerifyBackend Backend(&Generated, &Goals);
  for (const ObligationModule &Module : Modules) {
    VerifyResult Result = Backend.verify(Module);
    if (Module.BMCTransform)
      Result.Bound = Module.BMCTransform->UnrollBound;
    Replay.Results.push_back(std::move(Result));
  }
  Error = Project.writeLeanProjectModules(Generated);
  if (!Error)
    Error = Project.finalizeLeanProject(Goals, nullptr);
  if (!Error && Opts.LeanAuto)
    Project.automateLeanProject(Goals);
  report();
  if (Error) {
    Replay.Error = "cannot finalize Lean project (" +
                   llvm::toString(std::move(Error)) + ")";
    return Replay;
  }
  const std::set<std::string> Automatic = Project.automaticLeanGoals(Goals);
  for (const VerifyResult &Result : Replay.Results)
    Replay.Automatic.push_back(llvm::count_if(
        std::set<std::string>(Result.LeanGoals.begin(), Result.LeanGoals.end()),
        [&](const std::string &Goal) { return Automatic.count(Goal); }));
  if (!Opts.LeanCertify || interruptRequested())
    return Replay;

  // A module is proved when each of its goals is certified. A bounded one
  // whose unwinding goals alone are not is safe within its bound: Lean
  // proves goals, and never refutes one.
  // As for source certification: the Expected is tested once.
  std::optional<std::map<std::string, std::string>> Certified;
  std::string Failed;
  if (auto Checked = Project.certifyLeanProject(Goals))
    Certified = std::move(*Checked);
  else
    Failed = llvm::toString(Checked.takeError());
  std::map<std::string, const LeanProjectGoal *> GoalsByName;
  for (const LeanProjectGoal &Goal : Goals)
    GoalsByName.emplace(Goal.Name, &Goal);
  for (VerifyResult &Result : Replay.Results) {
    if (Result.Status != VerifyStatus::Exported)
      continue;
    std::string Reason = Failed;
    bool OnlyUnwinding = Failed.empty();
    if (Certified)
      for (const std::string &Goal : std::set<std::string>(
               Result.LeanGoals.begin(), Result.LeanGoals.end()))
        if (auto Failure = Certified->find(Goal); Failure != Certified->end()) {
          const LeanProjectGoal *Known = GoalsByName.at(Goal);
          OnlyUnwinding = OnlyUnwinding && Known->Unwinding;
          if (Result.ObligationId.empty())
            Result.ObligationId = Known->StableId;
          Reason += (Reason.empty() ? "" : "; ") +
                    std::string("the proof of ") + Known->StableId + ": " +
                    Failure->second;
        }
    if (Reason.empty()) {
      Result.Status = VerifyStatus::Verified;
      Result.Reason = VerifyReason::None;
      Result.Message.clear();
    } else if (Result.Bound && OnlyUnwinding) {
      Result.Status = VerifyStatus::BoundedSafe;
      Result.Reason = VerifyReason::IncompleteBound;
      Result.Message = "every goal is certified but the unwinding: no "
                       "execution within " +
                       std::to_string(*Result.Bound) +
                       " loop iterations fails (" + Reason + ")";
    } else {
      Result.Status = VerifyStatus::Unresolved;
      Result.Reason = VerifyReason::LeanExportFailure;
      Result.Message = "Lean certification failed: " + Reason;
    }
  }
  return Replay;
}