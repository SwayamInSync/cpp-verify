//===--- ObligationSimplify.cpp
//--------------------------------------------===//
#include "ObligationSimplify.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/CheckedArithmetic.h"
#include <map>
#include <algorithm>
#include <optional>
#include <set>

namespace clang {
namespace verify {

std::unique_ptr<LogicExpr> cloneLogicExpr(const LogicExpr *Expr) {
  if (!Expr)
    return nullptr;
  auto Copy = std::make_unique<LogicExpr>(Expr->K);
  Copy->Sort = Expr->Sort;
  Copy->Loc = Expr->Loc;
  Copy->EndLoc = Expr->EndLoc;
  Copy->Source = Expr->Source;
  Copy->IntVal = Expr->IntVal;
  Copy->BoolVal = Expr->BoolVal;
  Copy->Name = Expr->Name;
  Copy->Binder = Expr->Binder;
  Copy->OverflowOp = Expr->OverflowOp;
  Copy->CollectionOp = Expr->CollectionOp;
  Copy->SpecCallee = Expr->SpecCallee;
  for (const auto &Child : Expr->Children)
    Copy->Children.push_back(cloneLogicExpr(Child.get()));
  for (const auto &Pattern : Expr->Patterns)
    Copy->Patterns.push_back(cloneLogicExpr(Pattern.get()));
  return Copy;
}

namespace {

uint64_t countNodes(const LogicExpr *Expr) {
  if (!Expr)
    return 0;
  uint64_t Count = 1;
  for (const auto &Child : Expr->Children)
    Count += countNodes(Child.get());
  return Count;
}

uint64_t countModuleNodes(const ObligationModule &Module) {
  uint64_t Count = countNodes(Module.CorrectnessGoal.get()) +
                   countNodes(Module.CounterexampleQuery.get());
  for (const Obligation &Item : Module.Obligations)
    Count += countNodes(Item.Goal.get()) +
             countNodes(Item.CounterexampleQuery.get());
  for (const auto &[Identity, Function] : Module.LogicFunctions) {
    (void)Identity;
    Count += countNodes(Function.StepDefinition.get());
    for (const auto &Definition : Function.DefinitionLevels)
      Count += countNodes(Definition.get());
  }
  return Count;
}

std::optional<bool> boolConstant(const LogicExpr *Expr) {
  if (!Expr || Expr->Sort.Kind != LogicSortKind::Bool)
    return std::nullopt;
  if (Expr->K == LogicExpr::True)
    return true;
  if (Expr->K == LogicExpr::False)
    return false;
  if (Expr->K == LogicExpr::BoolLit)
    return Expr->BoolVal;
  return std::nullopt;
}

bool equalLogicExpr(const LogicExpr *Left, const LogicExpr *Right) {
  if (!Left || !Right)
    return Left == Right;
  if (Left->K != Right->K || Left->Sort.Kind != Right->Sort.Kind ||
      Left->Sort.BitWidth != Right->Sort.BitWidth ||
      Left->Sort.Signedness != Right->Sort.Signedness ||
      Left->IntVal != Right->IntVal || Left->BoolVal != Right->BoolVal ||
      Left->Name != Right->Name || Left->Binder != Right->Binder ||
      Left->OverflowOp != Right->OverflowOp ||
      Left->CollectionOp != Right->CollectionOp ||
      Left->SpecCallee != Right->SpecCallee ||
      Left->Children.size() != Right->Children.size())
    return false;
  for (unsigned I = 0; I != Left->Children.size(); ++I)
    if (!equalLogicExpr(Left->Children[I].get(), Right->Children[I].get()))
      return false;
  return true;
}

std::unique_ptr<LogicExpr> boolLiteral(bool Value, const LogicExpr &Source) {
  auto Result =
      std::make_unique<LogicExpr>(Value ? LogicExpr::True : LogicExpr::False);
  Result->Sort = LogicSort::boolSort();
  Result->Loc = Source.Loc;
  Result->EndLoc = Source.EndLoc;
  Result->Source = Source.Source;
  return Result;
}

bool isPositiveDivisor(const LogicExpr *Expr, const LogicSort &SourceSort) {
  if (!Expr || Expr->K != LogicExpr::IntLit ||
      Expr->Sort.Kind != LogicSortKind::MathematicalInteger ||
      Expr->IntVal.empty() || Expr->IntVal.front() == '-' ||
      llvm::APInt::getBitsNeeded(Expr->IntVal, 10) > SourceSort.BitWidth)
    return false;
  return !llvm::APInt(SourceSort.BitWidth, Expr->IntVal, 10).isZero();
}

std::optional<LogicSort> unsignedMathSourceSort(const LogicExpr *Expr) {
  if (!Expr)
    return std::nullopt;
  if (Expr->K == LogicExpr::BvToInt && Expr->Children.size() == 1 &&
      Expr->Children[0] &&
      Expr->Children[0]->Sort.Kind == LogicSortKind::BitVector &&
      Expr->Children[0]->Sort.Signedness == LogicSignedness::Unsigned)
    return Expr->Children[0]->Sort;
  if ((Expr->K != LogicExpr::Div && Expr->K != LogicExpr::Rem) ||
      Expr->Sort.Kind != LogicSortKind::MathematicalInteger ||
      Expr->Children.size() != 2)
    return std::nullopt;
  std::optional<LogicSort> SourceSort =
      unsignedMathSourceSort(Expr->Children[0].get());
  if (!SourceSort || !isPositiveDivisor(Expr->Children[1].get(), *SourceSort))
    return std::nullopt;
  return SourceSort;
}

std::unique_ptr<LogicExpr>
lowerUnsignedMathArithmetic(std::unique_ptr<LogicExpr> Expr,
                            const LogicSort &SourceSort) {
  if (Expr->K == LogicExpr::BvToInt)
    return std::move(Expr->Children.front());

  auto Divisor = std::make_unique<LogicExpr>(LogicExpr::IntLit);
  Divisor->Sort = SourceSort;
  Divisor->Loc = Expr->Children[1]->Loc;
  Divisor->EndLoc = Expr->Children[1]->EndLoc;
  Divisor->Source = Expr->Children[1]->Source;
  Divisor->IntVal = Expr->Children[1]->IntVal;

  auto MachineArithmetic = std::make_unique<LogicExpr>(Expr->K);
  MachineArithmetic->Sort = SourceSort;
  MachineArithmetic->Loc = Expr->Loc;
  MachineArithmetic->EndLoc = Expr->EndLoc;
  MachineArithmetic->Source = Expr->Source;
  MachineArithmetic->Children.push_back(
      lowerUnsignedMathArithmetic(std::move(Expr->Children[0]), SourceSort));
  MachineArithmetic->Children.push_back(std::move(Divisor));
  return MachineArithmetic;
}

std::unique_ptr<LogicExpr>
simplifyUnsignedMathToBitVector(std::unique_ptr<LogicExpr> Expr,
                                ObligationSimplificationStats &Stats) {
  if (!Expr || Expr->K != LogicExpr::IntToBv ||
      Expr->Sort.Kind != LogicSortKind::BitVector || Expr->Children.size() != 1)
    return Expr;

  LogicExpr *Arithmetic = Expr->Children.front().get();
  if (!Arithmetic ||
      (Arithmetic->K != LogicExpr::Div && Arithmetic->K != LogicExpr::Rem) ||
      Arithmetic->Sort.Kind != LogicSortKind::MathematicalInteger ||
      Arithmetic->Children.size() != 2)
    return Expr;

  std::optional<LogicSort> SourceSort = unsignedMathSourceSort(Arithmetic);
  if (!SourceSort)
    return Expr;
  auto MachineArithmetic = lowerUnsignedMathArithmetic(
      std::move(Expr->Children.front()), *SourceSort);
  ++Stats.Rewrites;
  if (Expr->Sort.BitWidth == SourceSort->BitWidth &&
      Expr->Sort.Signedness == SourceSort->Signedness)
    return MachineArithmetic;

  auto Resize = std::make_unique<LogicExpr>(LogicExpr::BvResize);
  Resize->Sort = Expr->Sort;
  Resize->Loc = Expr->Loc;
  Resize->EndLoc = Expr->EndLoc;
  Resize->Source = Expr->Source;
  Resize->Children.push_back(std::move(MachineArithmetic));
  return Resize;
}

std::unique_ptr<LogicExpr> simplifyExpr(std::unique_ptr<LogicExpr> Expr,
                                        ObligationSimplificationStats &Stats) {
  if (!Expr)
    return nullptr;
  for (auto &Child : Expr->Children)
    Child = simplifyExpr(std::move(Child), Stats);

  if ((Expr->K == LogicExpr::Eq || Expr->K == LogicExpr::Ne) &&
      Expr->Children.size() == 2 &&
      equalLogicExpr(Expr->Children[0].get(), Expr->Children[1].get())) {
    ++Stats.Rewrites;
    return boolLiteral(Expr->K == LogicExpr::Eq, *Expr);
  }

  if (Expr->K == LogicExpr::Not && Expr->Children.size() == 1) {
    if (std::optional<bool> Value =
            boolConstant(Expr->Children.front().get())) {
      ++Stats.Rewrites;
      return boolLiteral(!*Value, *Expr);
    }
    LogicExpr *Child = Expr->Children.front().get();
    if (Child && Child->K == LogicExpr::Not && Child->Children.size() == 1 &&
        Child->Children.front() &&
        Child->Children.front()->Sort.Kind == LogicSortKind::Bool) {
      ++Stats.Rewrites;
      return std::move(Child->Children.front());
    }
  }

  if ((Expr->K == LogicExpr::And || Expr->K == LogicExpr::Or) &&
      Expr->Children.size() == 2) {
    std::optional<bool> Left = boolConstant(Expr->Children[0].get());
    std::optional<bool> Right = boolConstant(Expr->Children[1].get());
    if (Left) {
      const bool SelectRight = Expr->K == LogicExpr::And ? *Left : !*Left;
      ++Stats.Rewrites;
      return SelectRight ? std::move(Expr->Children[1])
                         : boolLiteral(*Left, *Expr);
    }
    if (Right) {
      const bool SelectLeft = Expr->K == LogicExpr::And ? *Right : !*Right;
      ++Stats.Rewrites;
      return SelectLeft ? std::move(Expr->Children[0])
                        : boolLiteral(*Right, *Expr);
    }
  }

  if (Expr->K == LogicExpr::Ite && Expr->Children.size() == 3)
    if (std::optional<bool> Cond = boolConstant(Expr->Children.front().get())) {
      ++Stats.Rewrites;
      return std::move(Expr->Children[*Cond ? 1 : 2]);
    }

  return simplifyUnsignedMathToBitVector(std::move(Expr), Stats);
}

std::unique_ptr<LogicExpr> negate(std::unique_ptr<LogicExpr> Expr) {
  auto Result = std::make_unique<LogicExpr>(LogicExpr::Not);
  Result->Sort = LogicSort::boolSort();
  if (Expr) {
    Result->Loc = Expr->Loc;
    Result->EndLoc = Expr->EndLoc;
    Result->Source = Expr->Source;
  }
  Result->Children.push_back(std::move(Expr));
  return Result;
}

std::unique_ptr<LogicExpr>
buildCompleteGoal(const std::vector<Obligation> &Obligations) {
  if (Obligations.empty()) {
    auto Result = std::make_unique<LogicExpr>(LogicExpr::True);
    Result->Sort = LogicSort::boolSort();
    return Result;
  }
  auto Complete = cloneLogicExpr(Obligations.front().Goal.get());
  for (unsigned I = 1; I != Obligations.size(); ++I) {
    auto Conjunction = std::make_unique<LogicExpr>(LogicExpr::And);
    Conjunction->Sort = LogicSort::boolSort();
    Conjunction->Loc = Complete->Loc;
    Conjunction->EndLoc = Complete->EndLoc;
    Conjunction->Source = Complete->Source;
    Conjunction->Children.push_back(std::move(Complete));
    Conjunction->Children.push_back(cloneLogicExpr(Obligations[I].Goal.get()));
    Complete = std::move(Conjunction);
  }
  return Complete;
}

void collectCalledFunctions(const LogicExpr *Expr,
                            std::set<std::string> &Called) {
  if (!Expr)
    return;
  if (Expr->K == LogicExpr::SpecCall)
    Called.insert(Expr->SpecCallee);
  for (const auto &Child : Expr->Children)
    collectCalledFunctions(Child.get(), Called);
}

bool callsOnlyReachableFunctions(const LogicExpr *Expr,
                                 const std::set<std::string> &Reachable) {
  std::set<std::string> Called;
  collectCalledFunctions(Expr, Called);
  return std::all_of(
      Called.begin(), Called.end(),
      [&](const std::string &Name) { return Reachable.count(Name) != 0; });
}

void simplifyFunctions(ObligationModule &Module,
                       ObligationSimplificationStats &Stats) {
  for (auto &[Identity, Function] : Module.LogicFunctions) {
    (void)Identity;
    Function.StepDefinition =
        simplifyExpr(std::move(Function.StepDefinition), Stats);
    for (auto &Definition : Function.DefinitionLevels)
      Definition = simplifyExpr(std::move(Definition), Stats);
  }

  std::set<std::string> Reachable;
  for (const Obligation &Item : Module.Obligations)
    collectCalledFunctions(Item.Goal.get(), Reachable);
  std::vector<std::string> Pending(Reachable.begin(), Reachable.end());
  for (unsigned I = 0; I != Pending.size(); ++I) {
    auto Function = Module.LogicFunctions.find(Pending[I]);
    if (Function == Module.LogicFunctions.end())
      continue;
    std::set<std::string> Dependencies;
    collectCalledFunctions(Function->second.StepDefinition.get(), Dependencies);
    for (const auto &Definition : Function->second.DefinitionLevels)
      collectCalledFunctions(Definition.get(), Dependencies);
    for (const std::string &Dependency : Dependencies)
      if (Reachable.insert(Dependency).second)
        Pending.push_back(Dependency);
  }

  for (DiagnosticTraceEvent &Event : Module.TraceEvents) {
    if (!callsOnlyReachableFunctions(Event.Guard.get(), Reachable)) {
      Event.Guard = boolLiteral(false, *Event.Guard);
      Event.Values.clear();
      continue;
    }
    Event.Values.erase(std::remove_if(Event.Values.begin(), Event.Values.end(),
                                      [&](const DiagnosticTraceValue &Value) {
                                        return !callsOnlyReachableFunctions(
                                            Value.Value.get(), Reachable);
                                      }),
                       Event.Values.end());
  }

  for (auto It = Module.LogicFunctions.begin();
       It != Module.LogicFunctions.end();) {
    if (Reachable.count(It->first)) {
      ++It;
      continue;
    }
    // Kept only for a counterexample check's unfoldings and postconditions.
    Module.EvidenceFunctions.emplace(It->first, std::move(It->second));
    It = Module.LogicFunctions.erase(It);
    ++Stats.FunctionsRemoved;
  }
}

} // namespace

namespace {

void collectNames(const LogicExpr *Expr, std::set<std::string> &Names) {
  if (!Expr)
    return;
  if (Expr->K == LogicExpr::Var)
    Names.insert(Expr->Name);
  if (Expr->K == LogicExpr::Forall || Expr->K == LogicExpr::Exists)
    Names.insert(Expr->Binder);
  for (const auto &Child : Expr->Children)
    collectNames(Child.get(), Names);
}

void collectArgumentVariables(
    const LogicExpr *Expr, bool InArgument, std::set<std::string> &Bound,
    std::set<std::string> &Seen,
    std::vector<std::pair<std::string, LogicSort>> &Out) {
  if (!Expr)
    return;
  if (Expr->K == LogicExpr::Var && InArgument && !Bound.count(Expr->Name) &&
      (Expr->Sort.Kind == LogicSortKind::MathematicalInteger ||
       Expr->Sort.Kind == LogicSortKind::BitVector) &&
      Seen.insert(Expr->Name).second)
    Out.emplace_back(Expr->Name, Expr->Sort);
  const bool Quantifier =
      Expr->K == LogicExpr::Forall || Expr->K == LogicExpr::Exists;
  const bool Inserted = Quantifier && Bound.insert(Expr->Binder).second;
  for (const auto &Child : Expr->Children)
    collectArgumentVariables(Child.get(),
                             InArgument || Expr->K == LogicExpr::SpecCall,
                             Bound, Seen, Out);
  if (Inserted)
    Bound.erase(Expr->Binder);
}

std::unique_ptr<LogicExpr> substituteVariable(const LogicExpr *Expr,
                                              const std::string &Name,
                                              const LogicExpr &Value) {
  if (!Expr)
    return nullptr;
  if (Expr->K == LogicExpr::Var && Expr->Name == Name)
    return cloneLogicExpr(&Value);
  auto Copy = std::make_unique<LogicExpr>(Expr->K);
  Copy->Sort = Expr->Sort;
  Copy->Loc = Expr->Loc;
  Copy->EndLoc = Expr->EndLoc;
  Copy->Source = Expr->Source;
  Copy->IntVal = Expr->IntVal;
  Copy->BoolVal = Expr->BoolVal;
  Copy->Name = Expr->Name;
  Copy->Binder = Expr->Binder;
  Copy->OverflowOp = Expr->OverflowOp;
  Copy->CollectionOp = Expr->CollectionOp;
  Copy->SpecCallee = Expr->SpecCallee;
  for (const auto &Child : Expr->Children)
    Copy->Children.push_back(substituteVariable(Child.get(), Name, Value));
  for (const auto &Pattern : Expr->Patterns)
    Copy->Patterns.push_back(substituteVariable(Pattern.get(), Name, Value));
  return Copy;
}

std::unique_ptr<LogicExpr> logicNode(LogicExpr::Kind K, LogicSort Sort,
                                     const LogicExpr &At) {
  auto Node = std::make_unique<LogicExpr>(K);
  Node->Sort = Sort;
  Node->Loc = At.Loc;
  Node->EndLoc = At.EndLoc;
  Node->Source = At.Source;
  return Node;
}

void collectBinders(const LogicExpr *Expr, std::set<std::string> &Binders) {
  if (!Expr)
    return;
  if (Expr->K == LogicExpr::Forall || Expr->K == LogicExpr::Exists)
    Binders.insert(Expr->Binder);
  for (const auto &Child : Expr->Children)
    collectBinders(Child.get(), Binders);
}

bool mentionsAny(const LogicExpr *Expr, const std::set<std::string> &Names) {
  if (!Expr)
    return false;
  if (Expr->K == LogicExpr::Var && Names.count(Expr->Name))
    return true;
  for (const auto &Child : Expr->Children)
    if (mentionsAny(Child.get(), Names))
      return true;
  return false;
}

/// The definition x == t that \p Expr states, if x may be replaced by t.
std::optional<std::pair<std::string, const LogicExpr *>>
definitionIn(const LogicExpr *Expr, const std::string &Keep,
             const std::set<std::string> &Binders) {
  if (!Expr || Expr->K != LogicExpr::Eq || Expr->Children.size() != 2)
    return std::nullopt;
  for (unsigned Side : {0U, 1U}) {
    const LogicExpr *Var = Expr->Children[Side].get();
    const LogicExpr *Value = Expr->Children[1 - Side].get();
    if (Var->K != LogicExpr::Var || Var->Name == Keep ||
        Binders.count(Var->Name) ||
        (Var->Sort.Kind != LogicSortKind::MathematicalInteger &&
         Var->Sort.Kind != LogicSortKind::BitVector &&
         Var->Sort.Kind != LogicSortKind::Bool &&
         Var->Sort.Kind != LogicSortKind::Pointer))
      continue;
    std::set<std::string> Names = Binders;
    Names.insert(Var->Name);
    if (!mentionsAny(Value, Names))
      return std::make_pair(Var->Name, Value);
  }
  return std::nullopt;
}

/// Substitutes the definitions assumed by implications where \p Expr is
/// antitone: (x == t && A) -> B becomes (A -> B)[x := t], which is no
/// weaker there, so the result has a model whenever \p Expr has.
std::unique_ptr<LogicExpr>
eliminateDefinitions(const LogicExpr *Expr, bool Antitone,
                     const std::string &Keep,
                     const std::set<std::string> &Binders, unsigned &Budget) {
  if (!Expr)
    return nullptr;
  if (Antitone && Expr->K == LogicExpr::Or && Budget != 0) {
    for (unsigned I = 0; I != Expr->Children.size(); ++I) {
      const LogicExpr *Child = Expr->Children[I].get();
      if (Child->K != LogicExpr::Not || Child->Children.size() != 1)
        continue;
      const LogicExpr *Assumed = Child->Children.front().get();
      std::vector<const LogicExpr *> Conjuncts;
      std::vector<const LogicExpr *> Work{Assumed};
      while (!Work.empty()) {
        const LogicExpr *Next = Work.back();
        Work.pop_back();
        if (Next->K == LogicExpr::And)
          for (auto It = Next->Children.rbegin(); It != Next->Children.rend();
               ++It)
            Work.push_back(It->get());
        else
          Conjuncts.push_back(Next);
      }
      for (unsigned J = 0; J != Conjuncts.size(); ++J) {
        auto Definition = definitionIn(Conjuncts[J], Keep, Binders);
        if (!Definition)
          continue;
        --Budget;
        auto Rest = logicNode(LogicExpr::And, LogicSort::boolSort(), *Assumed);
        for (unsigned K = 0; K != Conjuncts.size(); ++K)
          if (K != J)
            Rest->Children.push_back(cloneLogicExpr(Conjuncts[K]));
        auto TrueNode =
            logicNode(LogicExpr::True, LogicSort::boolSort(), *Assumed);
        auto Rewritten = logicNode(LogicExpr::Or, LogicSort::boolSort(), *Expr);
        for (unsigned K = 0; K != Expr->Children.size(); ++K) {
          if (K != I) {
            Rewritten->Children.push_back(
                cloneLogicExpr(Expr->Children[K].get()));
            continue;
          }
          Rewritten->Children.push_back(negate(
              Rest->Children.empty() ? std::move(TrueNode) : std::move(Rest)));
        }
        auto Substituted = substituteVariable(
            Rewritten.get(), Definition->first, *Definition->second);
        return eliminateDefinitions(Substituted.get(), Antitone, Keep, Binders,
                                    Budget);
      }
    }
  }
  auto Copy = std::make_unique<LogicExpr>(Expr->K);
  Copy->Sort = Expr->Sort;
  Copy->Loc = Expr->Loc;
  Copy->EndLoc = Expr->EndLoc;
  Copy->Source = Expr->Source;
  Copy->IntVal = Expr->IntVal;
  Copy->BoolVal = Expr->BoolVal;
  Copy->Name = Expr->Name;
  Copy->Binder = Expr->Binder;
  Copy->OverflowOp = Expr->OverflowOp;
  Copy->CollectionOp = Expr->CollectionOp;
  Copy->SpecCallee = Expr->SpecCallee;
  const bool Monotone = Expr->K == LogicExpr::And || Expr->K == LogicExpr::Or ||
                        Expr->K == LogicExpr::Not ||
                        Expr->K == LogicExpr::Forall ||
                        Expr->K == LogicExpr::Exists;
  for (unsigned I = 0; I != Expr->Children.size(); ++I) {
    const LogicExpr *Child = Expr->Children[I].get();
    const bool Body =
        (Expr->K != LogicExpr::Forall && Expr->K != LogicExpr::Exists) ||
        I + 1 == Expr->Children.size();
    if (!Monotone || !Body) {
      Copy->Children.push_back(cloneLogicExpr(Child));
      continue;
    }
    Copy->Children.push_back(eliminateDefinitions(
        Child, Expr->K == LogicExpr::Not ? !Antitone : Antitone, Keep, Binders,
        Budget));
  }
  return Copy;
}

} // namespace

std::vector<std::pair<std::string, LogicSort>>
inductionVariables(const ObligationModule &Module, const Obligation *Item) {
  std::vector<std::pair<std::string, LogicSort>> Out;
  std::set<std::string> Bound;
  std::set<std::string> Seen;
  collectArgumentVariables(Item ? Item->CounterexampleQuery.get()
                                : Module.CounterexampleQuery.get(),
                           false, Bound, Seen, Out);
  return Out;
}

std::string inductionNote(const ObligationModule &Module,
                          const std::vector<std::string> &Variables) {
  if (Variables.empty())
    return {};
  std::string Names;
  for (const std::string &Variable : Variables) {
    auto It = Module.DiagnosticVariables.find(Variable);
    Names += (Names.empty() ? "" : ", ") +
             (It != Module.DiagnosticVariables.end() ? It->second.DisplayName
                                                     : Variable);
  }
  return "; strong induction on " + Names +
         ", assuming the goal at every smaller nonnegative value with all else "
         "fixed, did not settle it";
}

llvm::Expected<ObligationModule> inductionModule(const ObligationModule &Module,
                                                 const std::string &Variable,
                                                 const LogicSort &Sort,
                                                 const Obligation *Item) {
  // An unwinding obligation is read with bounded semantics on its own.
  const bool Unwinds =
      Item ? Item->Kind == ObligationKind::Unwinding
           : std::any_of(Module.Obligations.begin(), Module.Obligations.end(),
                         [](const Obligation &Each) {
                           return Each.Kind == ObligationKind::Unwinding;
                         });
  const LogicExpr *Original =
      Item ? Item->CounterexampleQuery.get() : Module.CounterexampleQuery.get();
  if (!Original || Module.Obligations.empty() || Unwinds ||
      (Sort.Kind != LogicSortKind::MathematicalInteger &&
       Sort.Kind != LogicSortKind::BitVector))
    return llvm::createStringError(llvm::inconvertibleErrorCode(),
                                   "no induction over this module");
  std::set<std::string> Binders;
  collectBinders(Original, Binders);
  // A query with the assumed definitions substituted has a model whenever
  // the original has, and only then is the hypothesis about the variable.
  unsigned Budget = 256;
  auto Eliminated =
      eliminateDefinitions(Original, false, Variable, Binders, Budget);
  if (countNodes(Eliminated.get()) > 4 * countNodes(Original) + 10000)
    Eliminated = cloneLogicExpr(Original);
  const LogicExpr &Query = *Eliminated;
  std::set<std::string> Names;
  collectNames(&Query, Names);
  for (const auto &[Identity, Function] : Module.LogicFunctions) {
    (void)Identity;
    collectNames(Function.StepDefinition.get(), Names);
    for (const auto &Definition : Function.DefinitionLevels)
      collectNames(Definition.get(), Names);
  }
  std::string Binder = "__induction_" + Variable;
  while (Names.count(Binder))
    Binder += "_";

  const LogicSort MathSort = LogicSort::mathematicalInteger();
  auto Smaller = logicNode(LogicExpr::Var, MathSort, Query);
  Smaller->Name = Binder;
  auto Current = logicNode(LogicExpr::Var, Sort, Query);
  Current->Name = Variable;
  std::unique_ptr<LogicExpr> Hi;
  if (Sort.Kind == LogicSortKind::BitVector) {
    auto Converted = logicNode(LogicExpr::IntToBv, Sort, Query);
    Converted->Children.push_back(std::move(Smaller));
    Smaller = std::move(Converted);
    Hi = logicNode(LogicExpr::BvToInt,
                   LogicSort::mathematicalInteger(Sort.BitWidth,
                                                  Sort.Signedness ==
                                                      LogicSignedness::Signed),
                   Query);
    Hi->Children.push_back(std::move(Current));
  } else {
    Hi = std::move(Current);
  }
  auto Lo = logicNode(LogicExpr::IntLit, MathSort, Query);
  Lo->IntVal = "0";
  auto Hypothesis = logicNode(LogicExpr::Forall, LogicSort::boolSort(), Query);
  Hypothesis->Binder = Binder;
  Hypothesis->Children.push_back(std::move(Lo));
  Hypothesis->Children.push_back(std::move(Hi));
  Hypothesis->Children.push_back(
      negate(substituteVariable(&Query, Variable, *Smaller)));
  auto Least = logicNode(LogicExpr::And, LogicSort::boolSort(), Query);
  Least->Children.push_back(std::move(Hypothesis));
  Least->Children.push_back(cloneLogicExpr(&Query));

  ObligationModule Result;
  Result.FunctionName = Module.FunctionName;
  Result.FunctionIdentity = Module.FunctionIdentity;
  Result.BMCTransform = Module.BMCTransform;
  Result.DiagnosticVariables = Module.DiagnosticVariables;
  Result.ResultVarName = Module.ResultVarName;
  Result.HeapPrefix = Module.HeapPrefix;
  auto copy = [](const LogicFunctionDecl &Function) {
    LogicFunctionDecl Copy;
    Copy.Identity = Function.Identity;
    Copy.DisplayName = Function.DisplayName;
    Copy.Parameters = Function.Parameters;
    Copy.ResultSort = Function.ResultSort;
    Copy.DefinitionFuel = Function.DefinitionFuel;
    Copy.Choice = Function.Choice;
    Copy.StepDefinition = cloneLogicExpr(Function.StepDefinition.get());
    for (const auto &Definition : Function.DefinitionLevels)
      Copy.DefinitionLevels.push_back(cloneLogicExpr(Definition.get()));
    Copy.Unfolding = cloneLogicExpr(Function.Unfolding.get());
    for (const auto &Post : Function.Postconditions)
      Copy.Postconditions.push_back(cloneLogicExpr(Post.get()));
    return Copy;
  };
  for (const auto &[Identity, Function] : Module.LogicFunctions)
    Result.LogicFunctions.emplace(Identity, copy(Function));
  for (const auto &[Identity, Function] : Module.EvidenceFunctions)
    Result.EvidenceFunctions.emplace(Identity, copy(Function));
  Result.AssumedPosts = Module.AssumedPosts;
  Result.AssumedUnfoldings = Module.AssumedUnfoldings;
  Result.Given = Module.Given;
  const Obligation &First = Item ? *Item : Module.Obligations.front();
  Obligation Inductive;
  Inductive.Id = First.Id;
  Inductive.StableId = First.StableId;
  Inductive.Kind = First.Kind;
  Inductive.Loc = First.Loc;
  Inductive.EndLoc = First.EndLoc;
  Inductive.Source = First.Source;
  Inductive.Goal = negate(std::move(Least));
  Inductive.CounterexampleQuery = negate(cloneLogicExpr(Inductive.Goal.get()));
  Result.CorrectnessGoal = cloneLogicExpr(Inductive.Goal.get());
  Result.CounterexampleQuery = negate(cloneLogicExpr(Inductive.Goal.get()));
  Result.Obligations.push_back(std::move(Inductive));
  auto Features = validateObligationModule(Result);
  if (!Features)
    return Features.takeError();
  Result.RequiredFeatures = *Features;
  return std::move(Result);
}

namespace {

/// An address as a sum of integer multiples of atomic terms and a constant,
/// read in a version of the heap named Family.
struct LinearAddress {
  std::map<std::string, std::pair<int64_t, const LogicExpr *>> Atoms;
  int64_t Constant = 0;
  std::string Family;
};

/// The heap a version belongs to: __heap_3 is a version of __heap.
std::optional<std::string> heapFamily(const LogicExpr *Heap) {
  if (!Heap || Heap->K != LogicExpr::Var)
    return std::nullopt;
  llvm::StringRef Name = Heap->Name;
  llvm::StringRef Stem = Name.rtrim("0123456789");
  if (Stem.size() == Name.size() || !Stem.consume_back("_"))
    return std::nullopt;
  return Stem.str();
}

bool isAddressSort(const LogicSort &Sort) {
  return Sort.Kind == LogicSortKind::Pointer ||
         Sort.Kind == LogicSortKind::MathematicalInteger;
}

std::string termKey(const LogicExpr *Expr) {
  std::string Key = "(" + std::to_string(Expr->K) + " " +
                    std::to_string(static_cast<int>(Expr->Sort.Kind)) + " " +
                    std::to_string(Expr->Sort.BitWidth) + " " +
                    std::to_string(static_cast<int>(Expr->Sort.Signedness)) +
                    " " + Expr->IntVal + " " + (Expr->BoolVal ? "1" : "0") +
                    " " + Expr->Name + " " + Expr->Binder + " " +
                    Expr->SpecCallee + " " +
                    std::to_string(static_cast<int>(Expr->OverflowOp)) + " " +
                    std::to_string(static_cast<int>(Expr->CollectionOp));
  for (const auto &Child : Expr->Children)
    Key += " " + termKey(Child.get());
  return Key + ")";
}

bool addLinear(const LogicExpr *Expr, int64_t Scale, LinearAddress &Out) {
  if (!Expr)
    return false;
  if (isAddressSort(Expr->Sort)) {
    int64_t Value = 0;
    switch (Expr->K) {
    case LogicExpr::IntLit: {
      if (llvm::StringRef(Expr->IntVal).getAsInteger(10, Value))
        return false;
      auto Product = llvm::checkedMul(Value, Scale);
      auto Sum = Product ? llvm::checkedAdd(Out.Constant, *Product)
                         : std::nullopt;
      if (!Sum)
        return false;
      Out.Constant = *Sum;
      return true;
    }
    case LogicExpr::BvToInt: {
      const LogicExpr *Machine =
          Expr->Children.size() == 1 ? Expr->Children[0].get() : nullptr;
      if (!Machine || Machine->K != LogicExpr::IntLit ||
          Machine->Sort.Kind != LogicSortKind::BitVector ||
          Machine->Sort.BitWidth == 0 || Machine->Sort.BitWidth > 64)
        break;
      const unsigned Width = Machine->Sort.BitWidth;
      const unsigned Parsed = std::max<unsigned>(
          Width + 1, static_cast<unsigned>(Machine->IntVal.size()) * 4 + 2);
      llvm::APInt Bits(Parsed, Machine->IntVal, 10);
      Bits = Bits.trunc(Width);
      if (Machine->Sort.Signedness != LogicSignedness::Signed &&
          Bits.isNegative() && Width == 64)
        break;
      Value = Machine->Sort.Signedness == LogicSignedness::Signed
                  ? Bits.getSExtValue()
                  : static_cast<int64_t>(Bits.getZExtValue());
      auto Product = llvm::checkedMul(Value, Scale);
      auto Sum = Product ? llvm::checkedAdd(Out.Constant, *Product)
                         : std::nullopt;
      if (!Sum)
        return false;
      Out.Constant = *Sum;
      return true;
    }
    case LogicExpr::Add:
      for (const auto &Child : Expr->Children)
        if (!addLinear(Child.get(), Scale, Out))
          return false;
      return true;
    case LogicExpr::Sub:
    case LogicExpr::Neg: {
      auto Negated = llvm::checkedMul(Scale, int64_t(-1));
      if (!Negated)
        return false;
      if (Expr->K == LogicExpr::Neg)
        return Expr->Children.size() == 1 &&
               addLinear(Expr->Children[0].get(), *Negated, Out);
      return Expr->Children.size() == 2 &&
             addLinear(Expr->Children[0].get(), Scale, Out) &&
             addLinear(Expr->Children[1].get(), *Negated, Out);
    }
    case LogicExpr::Mul:
      if (Expr->Children.size() == 2)
        for (unsigned I = 0; I != 2; ++I) {
          const LogicExpr *Factor = Expr->Children[I].get();
          if (Factor->K != LogicExpr::IntLit ||
              llvm::StringRef(Factor->IntVal).getAsInteger(10, Value))
            continue;
          auto Product = llvm::checkedMul(Value, Scale);
          return Product &&
                 addLinear(Expr->Children[1 - I].get(), *Product, Out);
        }
      break;
    default:
      break;
    }
  }
  auto &Slot = Out.Atoms[termKey(Expr)];
  Slot.second = Expr;
  auto Sum = llvm::checkedAdd(Slot.first, Scale);
  if (!Sum)
    return false;
  Slot.first = *Sum;
  if (Slot.first == 0)
    Out.Atoms.erase(termKey(Expr));
  return true;
}

/// The address a heap read reads, in linear form.
std::optional<LinearAddress> readAddress(const LogicExpr *Read) {
  if (!Read || Read->K != LogicExpr::Select || Read->Children.size() != 2)
    return std::nullopt;
  std::optional<std::string> Family = heapFamily(Read->Children[0].get());
  LinearAddress Out;
  if (!Family || !addLinear(Read->Children[1].get(), 1, Out))
    return std::nullopt;
  Out.Family = std::move(*Family);
  return Out;
}

void collectSelects(const LogicExpr *Expr,
                    std::vector<const LogicExpr *> &Out) {
  if (!Expr)
    return;
  if (Expr->K == LogicExpr::Select && Expr->Children.size() == 2)
    Out.push_back(Expr);
  for (const auto &Child : Expr->Children)
    collectSelects(Child.get(), Out);
}

void collectClosedAddresses(const LogicExpr *Expr,
                            std::set<std::string> &Bound,
                            std::set<std::string> &Seen,
                            std::vector<LinearAddress> &Out) {
  if (!Expr)
    return;
  if (Expr->K == LogicExpr::Select && Expr->Children.size() == 2 &&
      !mentionsAny(Expr->Children[1].get(), Bound))
    if (auto Address = readAddress(Expr))
      if (Seen.insert(Address->Family + termKey(Expr->Children[1].get()))
              .second)
        Out.push_back(std::move(*Address));
  const bool Quantifier =
      Expr->K == LogicExpr::Forall || Expr->K == LogicExpr::Exists;
  const bool Inserted = Quantifier && Bound.insert(Expr->Binder).second;
  for (const auto &Child : Expr->Children)
    collectClosedAddresses(Child.get(), Bound, Seen, Out);
  if (Inserted)
    Bound.erase(Expr->Binder);
}

class ReadInstantiator {
public:
  explicit ReadInstantiator(std::vector<LinearAddress> Reads)
      : Reads(std::move(Reads)) {}

  std::unique_ptr<LogicExpr> rewrite(const LogicExpr *Expr) {
    if (!Expr)
      return nullptr;
    auto Copy = logicNode(Expr->K, Expr->Sort, *Expr);
    Copy->IntVal = Expr->IntVal;
    Copy->BoolVal = Expr->BoolVal;
    Copy->Name = Expr->Name;
    Copy->Binder = Expr->Binder;
    Copy->OverflowOp = Expr->OverflowOp;
    Copy->CollectionOp = Expr->CollectionOp;
    Copy->SpecCallee = Expr->SpecCallee;
    for (const auto &Child : Expr->Children)
      Copy->Children.push_back(rewrite(Child.get()));
    for (const auto &Pattern : Expr->Patterns)
      Copy->Patterns.push_back(cloneLogicExpr(Pattern.get()));
    if (Expr->K != LogicExpr::Forall && Expr->K != LogicExpr::Exists)
      return Copy;
    std::vector<std::unique_ptr<LogicExpr>> Instances =
        instances(*Expr, *Copy);
    if (Instances.empty())
      return Copy;
    Added = true;
    auto Joined =
        logicNode(Expr->K == LogicExpr::Forall ? LogicExpr::And : LogicExpr::Or,
                  LogicSort::boolSort(), *Expr);
    Joined->Children.push_back(std::move(Copy));
    for (auto &Instance : Instances)
      Joined->Children.push_back(std::move(Instance));
    return Joined;
  }

  bool added() const { return Added; }

private:
  static constexpr unsigned MaxInstancesPerQuantifier = 16;
  static constexpr uint64_t MaxAddedNodes = 50000;

  std::vector<LinearAddress> Reads;
  uint64_t AddedNodes = 0;
  bool Added = false;

  /// The indices t at which the quantifier reads what a closed read reads:
  /// for a body read at Base + S * k, every closed read at Base + S * t.
  std::vector<std::unique_ptr<LogicExpr>> indices(const LogicExpr &Quantifier) {
    std::vector<std::unique_ptr<LogicExpr>> Out;
    std::vector<const LogicExpr *> BodyReads;
    if (Quantifier.Patterns.empty())
      collectSelects(Quantifier.Children.back().get(), BodyReads);
    else
      for (const auto &Pattern : Quantifier.Patterns)
        collectSelects(Pattern.get(), BodyReads);
    const std::set<std::string> Binder = {Quantifier.Binder};
    std::set<std::string> Seen;
    for (const LogicExpr *BodyRead : BodyReads) {
      std::optional<LinearAddress> Body = readAddress(BodyRead);
      if (!Body)
        continue;
      int64_t Stride = 0;
      bool Usable = true;
      for (auto It = Body->Atoms.begin(); It != Body->Atoms.end();) {
        const LogicExpr *Atom = It->second.second;
        if (Atom->K == LogicExpr::Var && Atom->Name == Quantifier.Binder) {
          Stride = It->second.first;
          It = Body->Atoms.erase(It);
          continue;
        }
        if (mentionsAny(Atom, Binder))
          Usable = false;
        ++It;
      }
      if (!Usable || Stride == 0 || Body->Atoms.empty())
        continue;
      for (const LinearAddress &Read : Reads) {
        if (Read.Family != Body->Family)
          continue;
        std::unique_ptr<LogicExpr> Index = indexOf(*Body, Stride, Read,
                                                   Quantifier);
        if (Index && Seen.insert(termKey(Index.get())).second)
          Out.push_back(std::move(Index));
        if (Out.size() == MaxInstancesPerQuantifier)
          return Out;
      }
    }
    return Out;
  }

  /// (Read - Body) / Stride, when it cancels Body's atoms and every
  /// remaining coefficient is a multiple of Stride.
  static std::unique_ptr<LogicExpr> indexOf(const LinearAddress &Body,
                                            int64_t Stride,
                                            const LinearAddress &Read,
                                            const LogicExpr &At) {
    for (const auto &[Key, Entry] : Body.Atoms) {
      auto It = Read.Atoms.find(Key);
      if (It == Read.Atoms.end() || It->second.first != Entry.first)
        return nullptr;
    }
    auto Offset = llvm::checkedSub(Read.Constant, Body.Constant);
    if (!Offset || *Offset % Stride != 0)
      return nullptr;
    const LogicSort Integer = LogicSort::mathematicalInteger();
    std::unique_ptr<LogicExpr> Sum;
    auto add = [&](std::unique_ptr<LogicExpr> Term) {
      if (!Sum) {
        Sum = std::move(Term);
        return;
      }
      auto Node = logicNode(LogicExpr::Add, Integer, At);
      Node->Children.push_back(std::move(Sum));
      Node->Children.push_back(std::move(Term));
      Sum = std::move(Node);
    };
    auto literal = [&](int64_t Value) {
      auto Node = logicNode(LogicExpr::IntLit, Integer, At);
      Node->IntVal = std::to_string(Value);
      return Node;
    };
    for (const auto &[Key, Entry] : Read.Atoms) {
      if (Body.Atoms.count(Key))
        continue;
      if (Entry.second->Sort.Kind != LogicSortKind::MathematicalInteger ||
          Entry.first % Stride != 0)
        return nullptr;
      const int64_t Coefficient = Entry.first / Stride;
      std::unique_ptr<LogicExpr> Term = cloneLogicExpr(Entry.second);
      if (Coefficient != 1) {
        auto Product = logicNode(LogicExpr::Mul, Integer, At);
        Product->Children.push_back(literal(Coefficient));
        Product->Children.push_back(std::move(Term));
        Term = std::move(Product);
      }
      add(std::move(Term));
    }
    if (*Offset != 0 || !Sum)
      add(literal(*Offset / Stride));
    return Sum;
  }

  std::vector<std::unique_ptr<LogicExpr>>
  instances(const LogicExpr &Original, const LogicExpr &Rewritten) {
    std::vector<std::unique_ptr<LogicExpr>> Out;
    const bool Bounded = Rewritten.Children.size() == 3;
    if (Bounded &&
        (Rewritten.Children[0]->Sort.Kind !=
             LogicSortKind::MathematicalInteger ||
         Rewritten.Children[1]->Sort.Kind !=
             LogicSortKind::MathematicalInteger))
      return Out;
    const bool Forall = Original.K == LogicExpr::Forall;
    const LogicExpr *Body = Rewritten.Children.back().get();
    const uint64_t BodyNodes = countNodes(Body);
    for (std::unique_ptr<LogicExpr> &Index : indices(Original)) {
      if (AddedNodes + BodyNodes > MaxAddedNodes)
        break;
      AddedNodes += BodyNodes;
      std::unique_ptr<LogicExpr> Instance =
          substituteVariable(Body, Original.Binder, *Index);
      if (Bounded) {
        auto Low = logicNode(LogicExpr::Le, LogicSort::boolSort(), Original);
        Low->Children.push_back(cloneLogicExpr(Rewritten.Children[0].get()));
        Low->Children.push_back(cloneLogicExpr(Index.get()));
        auto High = logicNode(LogicExpr::Lt, LogicSort::boolSort(), Original);
        High->Children.push_back(cloneLogicExpr(Index.get()));
        High->Children.push_back(cloneLogicExpr(Rewritten.Children[1].get()));
        auto Range = logicNode(LogicExpr::And, LogicSort::boolSort(), Original);
        Range->Children.push_back(std::move(Low));
        Range->Children.push_back(std::move(High));
        auto Joined = logicNode(Forall ? LogicExpr::Or : LogicExpr::And,
                                LogicSort::boolSort(), Original);
        if (Forall) {
          auto Outside =
              logicNode(LogicExpr::Not, LogicSort::boolSort(), Original);
          Outside->Children.push_back(std::move(Range));
          Joined->Children.push_back(std::move(Outside));
        } else {
          Joined->Children.push_back(std::move(Range));
        }
        Joined->Children.push_back(std::move(Instance));
        Instance = std::move(Joined);
      }
      Out.push_back(std::move(Instance));
    }
    return Out;
  }
};

/// Joins each closed sequence equality the query refutes with its
/// extensionality instance; see instantiateExtensionality.
class ExtensionalityInstantiator {
public:
  explicit ExtensionalityInstantiator(std::set<std::string> Binders)
      : Binders(std::move(Binders)) {}

  /// Polarity is 1 where the query asserts the term, -1 where it asserts the
  /// negation, and 0 where it does both or the term is an operand.
  std::unique_ptr<LogicExpr> rewrite(const LogicExpr *Expr, int Polarity) {
    if (!Expr)
      return nullptr;
    auto Copy = logicNode(Expr->K, Expr->Sort, *Expr);
    Copy->IntVal = Expr->IntVal;
    Copy->BoolVal = Expr->BoolVal;
    Copy->Name = Expr->Name;
    Copy->Binder = Expr->Binder;
    Copy->OverflowOp = Expr->OverflowOp;
    Copy->CollectionOp = Expr->CollectionOp;
    Copy->SpecCallee = Expr->SpecCallee;
    const bool Quantifier =
        Expr->K == LogicExpr::Forall || Expr->K == LogicExpr::Exists;
    const bool Inserted = Quantifier && Bound.insert(Expr->Binder).second;
    for (size_t I = 0; I != Expr->Children.size(); ++I)
      Copy->Children.push_back(
          rewrite(Expr->Children[I].get(), childPolarity(*Expr, I, Polarity)));
    if (Inserted)
      Bound.erase(Expr->Binder);
    for (const auto &Pattern : Expr->Patterns)
      Copy->Patterns.push_back(cloneLogicExpr(Pattern.get()));
    const bool Refuted = (Expr->K == LogicExpr::Eq && Polarity < 0) ||
                         (Expr->K == LogicExpr::Ne && Polarity > 0);
    if (!Refuted || Expr->Children.size() != 2 ||
        Expr->Children[0]->Sort.Kind != LogicSortKind::Seq ||
        mentionsAny(Expr, Bound) || Instances == MaxInstances)
      return Copy;
    ++Instances;
    std::unique_ptr<LogicExpr> Extensional =
        extensional(*Copy->Children[0], *Copy->Children[1], *Expr);
    if (Expr->K == LogicExpr::Eq) {
      auto Joined = logicNode(LogicExpr::Or, LogicSort::boolSort(), *Expr);
      Joined->Children.push_back(std::move(Copy));
      Joined->Children.push_back(std::move(Extensional));
      return Joined;
    }
    auto Different = logicNode(LogicExpr::Not, LogicSort::boolSort(), *Expr);
    Different->Children.push_back(std::move(Extensional));
    auto Joined = logicNode(LogicExpr::And, LogicSort::boolSort(), *Expr);
    Joined->Children.push_back(std::move(Copy));
    Joined->Children.push_back(std::move(Different));
    return Joined;
  }

  bool added() const { return Instances != 0; }

private:
  static constexpr unsigned MaxInstances = 64;

  std::set<std::string> Binders;
  std::set<std::string> Bound;
  unsigned Instances = 0;

  static int childPolarity(const LogicExpr &Parent, size_t Index,
                           int Polarity) {
    switch (Parent.K) {
    case LogicExpr::Not:
      return -Polarity;
    case LogicExpr::And:
    case LogicExpr::Or:
      return Polarity;
    case LogicExpr::Ite:
      return Parent.Sort.Kind == LogicSortKind::Bool && Index != 0 ? Polarity
                                                                   : 0;
    case LogicExpr::Forall:
    case LogicExpr::Exists:
      return Index + 1 == Parent.Children.size() ? Polarity : 0;
    default:
      return 0;
    }
  }

  /// len(a) == len(b) && forall k in [0, len(a)). a[k] == b[k]
  std::unique_ptr<LogicExpr> extensional(const LogicExpr &A, const LogicExpr &B,
                                         const LogicExpr &At) {
    const LogicSort Integer = LogicSort::mathematicalInteger(64);
    std::string Binder;
    do
      Binder = "__cppverify_ext" + std::to_string(Binders.size());
    while (!Binders.insert(Binder).second);
    auto collection = [&](LogicCollectionOp Op, LogicSort Sort,
                          std::unique_ptr<LogicExpr> Sequence,
                          std::unique_ptr<LogicExpr> Index) {
      auto Node = logicNode(LogicExpr::Collection, Sort, At);
      Node->CollectionOp = Op;
      Node->Children.push_back(std::move(Sequence));
      if (Index)
        Node->Children.push_back(std::move(Index));
      return Node;
    };
    auto length = [&](const LogicExpr &Sequence) {
      return collection(LogicCollectionOp::SeqLength, Integer,
                        cloneLogicExpr(&Sequence), nullptr);
    };
    auto read = [&](const LogicExpr &Sequence) {
      auto K = logicNode(LogicExpr::Var, Integer, At);
      K->Name = Binder;
      return collection(LogicCollectionOp::SeqIndex, Integer,
                        cloneLogicExpr(&Sequence), std::move(K));
    };
    auto equal = [&](std::unique_ptr<LogicExpr> L,
                     std::unique_ptr<LogicExpr> R) {
      auto Node = logicNode(LogicExpr::Eq, LogicSort::boolSort(), At);
      Node->Children.push_back(std::move(L));
      Node->Children.push_back(std::move(R));
      return Node;
    };
    auto Elements = logicNode(LogicExpr::Forall, LogicSort::boolSort(), At);
    Elements->Binder = Binder;
    auto Zero = logicNode(LogicExpr::IntLit, Integer, At);
    Zero->IntVal = "0";
    Elements->Children.push_back(std::move(Zero));
    Elements->Children.push_back(length(A));
    Elements->Children.push_back(equal(read(A), read(B)));
    auto Both = logicNode(LogicExpr::And, LogicSort::boolSort(), At);
    Both->Children.push_back(equal(length(A), length(B)));
    Both->Children.push_back(std::move(Elements));
    return Both;
  }
};

} // namespace

std::unique_ptr<LogicExpr> instantiateAtReads(const LogicExpr &Query) {
  std::set<std::string> Binders;
  collectBinders(&Query, Binders);
  if (Binders.empty())
    return nullptr;
  std::vector<LinearAddress> Reads;
  std::set<std::string> Bound;
  std::set<std::string> Seen;
  collectClosedAddresses(&Query, Bound, Seen, Reads);
  if (Reads.empty())
    return nullptr;
  ReadInstantiator Instantiator(std::move(Reads));
  std::unique_ptr<LogicExpr> Rewritten = Instantiator.rewrite(&Query);
  if (!Instantiator.added())
    return nullptr;
  return Rewritten;
}

std::unique_ptr<LogicExpr> instantiateExtensionality(const LogicExpr &Query) {
  std::set<std::string> Binders;
  collectBinders(&Query, Binders);
  ExtensionalityInstantiator Instantiator(std::move(Binders));
  std::unique_ptr<LogicExpr> Rewritten = Instantiator.rewrite(&Query, 1);
  if (!Instantiator.added())
    return nullptr;
  return Rewritten;
}

uint64_t obligationModuleNodeCount(const ObligationModule &Module) {
  return countModuleNodes(Module);
}

llvm::Expected<ObligationModule>
simplifyObligationModule(ObligationModule Module,
                         ObligationSimplificationStats *OutputStats) {
  auto InputFeatures = validateObligationModule(Module);
  if (!InputFeatures)
    return InputFeatures.takeError();
  if (*InputFeatures != Module.RequiredFeatures)
    return llvm::createStringError(
        llvm::inconvertibleErrorCode(),
        "cannot simplify an obligation module with stale feature metadata");

  ObligationSimplificationStats Stats;
  Stats.NodesBefore = countModuleNodes(Module);
  for (Obligation &Item : Module.Obligations) {
    Item.Goal = simplifyExpr(std::move(Item.Goal), Stats);
    Item.CounterexampleQuery = negate(cloneLogicExpr(Item.Goal.get()));
  }
  simplifyFunctions(Module, Stats);
  Module.CorrectnessGoal = buildCompleteGoal(Module.Obligations);
  Module.CounterexampleQuery =
      negate(cloneLogicExpr(Module.CorrectnessGoal.get()));

  auto RequiredFeatures = validateObligationModule(Module);
  if (!RequiredFeatures)
    return RequiredFeatures.takeError();
  Module.RequiredFeatures = *RequiredFeatures;
  auto FinalFeatures = validateObligationModule(Module);
  if (!FinalFeatures)
    return FinalFeatures.takeError();
  if (*FinalFeatures != Module.RequiredFeatures)
    return llvm::createStringError(
        llvm::inconvertibleErrorCode(),
        "canonical obligation simplification did not revalidate");

  Stats.NodesAfter = countModuleNodes(Module);
  if (OutputStats)
    *OutputStats = Stats;
  return std::move(Module);
}

} // namespace verify
} // namespace clang
