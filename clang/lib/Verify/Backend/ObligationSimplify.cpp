//===--- ObligationSimplify.cpp
//--------------------------------------------===//
#include "ObligationSimplify.h"
#include <algorithm>
#include <optional>
#include <set>

namespace clang {
namespace verify {
namespace {

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
  Copy->SpecCallee = Expr->SpecCallee;
  for (const auto &Child : Expr->Children)
    Copy->Children.push_back(cloneLogicExpr(Child.get()));
  return Copy;
}

uint64_t countNodes(const LogicExpr *Expr) {
  if (!Expr)
    return 0;
  uint64_t Count = 1;
  for (const auto &Child : Expr->Children)
    Count += countNodes(Child.get());
  return Count;
}

uint64_t countNodes(const ObligationModule &Module) {
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

  return Expr;
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
    It = Module.LogicFunctions.erase(It);
    ++Stats.FunctionsRemoved;
  }
}

} // namespace

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
  Stats.NodesBefore = countNodes(Module);
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

  Stats.NodesAfter = countNodes(Module);
  if (OutputStats)
    *OutputStats = Stats;
  return std::move(Module);
}

} // namespace verify
} // namespace clang
