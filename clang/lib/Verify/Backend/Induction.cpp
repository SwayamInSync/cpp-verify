//===--- Induction.cpp - Well-founded induction over obligation modules --===//
#include "Induction.h"
#include "LogicTerms.h"
#include <map>
#include <set>

namespace clang {
namespace verify {

namespace {

constexpr unsigned MaxFunctionSchemes = 3;
constexpr unsigned MaxVariableSchemes = 2;
/// How many other members of a recursion group an instance may pass through.
constexpr unsigned MaxGroupUnfolding = 3;
constexpr unsigned MaxInstances = 16;

std::unique_ptr<LogicExpr> node(LogicExpr::Kind K, LogicSort Sort,
                                const LogicExpr *At = nullptr) {
  auto Node = std::make_unique<LogicExpr>(K);
  Node->Sort = Sort;
  if (At) {
    Node->Loc = At->Loc;
    Node->EndLoc = At->EndLoc;
    Node->Source = At->Source;
  }
  return Node;
}

std::unique_ptr<LogicExpr> boolConstant(bool Value) {
  return node(Value ? LogicExpr::True : LogicExpr::False,
              LogicSort::boolSort());
}

std::unique_ptr<LogicExpr> intLiteral(const char *Value) {
  auto Literal = node(LogicExpr::IntLit, LogicSort::mathematicalInteger());
  Literal->IntVal = Value;
  return Literal;
}

std::unique_ptr<LogicExpr>
junction(LogicExpr::Kind K, std::vector<std::unique_ptr<LogicExpr>> Parts) {
  if (Parts.empty())
    return boolConstant(K == LogicExpr::And);
  // Canonical connectives are binary: nest them to the right.
  std::unique_ptr<LogicExpr> Result = std::move(Parts.back());
  for (size_t I = Parts.size() - 1; I-- > 0;) {
    auto Joined = node(K, LogicSort::boolSort(), Parts[I].get());
    Joined->Children.push_back(std::move(Parts[I]));
    Joined->Children.push_back(std::move(Result));
    Result = std::move(Joined);
  }
  return Result;
}

std::unique_ptr<LogicExpr> both(std::unique_ptr<LogicExpr> Left,
                                std::unique_ptr<LogicExpr> Right) {
  std::vector<std::unique_ptr<LogicExpr>> Parts;
  Parts.push_back(std::move(Left));
  Parts.push_back(std::move(Right));
  return junction(LogicExpr::And, std::move(Parts));
}

std::unique_ptr<LogicExpr> implies(std::unique_ptr<LogicExpr> Premise,
                                   std::unique_ptr<LogicExpr> Conclusion) {
  std::vector<std::unique_ptr<LogicExpr>> Parts;
  Parts.push_back(logicNot(std::move(Premise)));
  Parts.push_back(std::move(Conclusion));
  return junction(LogicExpr::Or, std::move(Parts));
}

std::unique_ptr<LogicExpr> compare(LogicExpr::Kind K,
                                   std::unique_ptr<LogicExpr> Left,
                                   std::unique_ptr<LogicExpr> Right) {
  auto Result = node(K, LogicSort::boolSort(), Left.get());
  Result->Children.push_back(std::move(Left));
  Result->Children.push_back(std::move(Right));
  return Result;
}

/// \p Expr as a mathematical integer.
std::unique_ptr<LogicExpr> asMath(std::unique_ptr<LogicExpr> Expr) {
  if (!Expr || Expr->Sort.Kind != LogicSortKind::BitVector)
    return Expr;
  auto Converted = node(LogicExpr::BvToInt,
                        LogicSort::mathematicalInteger(
                            Expr->Sort.BitWidth,
                            Expr->Sort.Signedness == LogicSignedness::Signed),
                        Expr.get());
  Converted->Children.push_back(std::move(Expr));
  return Converted;
}

/// The decrease relation of termination checks, on mathematical integers:
/// Lower is below Upper when, at the first component where they differ,
/// Upper's is nonnegative and Lower's smaller. It is well-founded.
std::unique_ptr<LogicExpr>
decrease(const std::vector<std::unique_ptr<LogicExpr>> &Lower,
         const std::vector<std::unique_ptr<LogicExpr>> &Upper) {
  std::vector<std::unique_ptr<LogicExpr>> Ways;
  for (size_t J = 0; J != Lower.size() && J != Upper.size(); ++J) {
    std::vector<std::unique_ptr<LogicExpr>> Parts;
    for (size_t I = 0; I != J; ++I)
      Parts.push_back(compare(LogicExpr::Eq,
                              asMath(cloneLogicExpr(Lower[I].get())),
                              asMath(cloneLogicExpr(Upper[I].get()))));
    Parts.push_back(compare(LogicExpr::Ge,
                            asMath(cloneLogicExpr(Upper[J].get())),
                            intLiteral("0")));
    Parts.push_back(compare(LogicExpr::Lt,
                            asMath(cloneLogicExpr(Lower[J].get())),
                            asMath(cloneLogicExpr(Upper[J].get()))));
    Ways.push_back(junction(LogicExpr::And, std::move(Parts)));
  }
  return junction(LogicExpr::Or, std::move(Ways));
}

void freeVariables(const LogicExpr *Expr, std::set<std::string> &Bound,
                   std::set<std::string> &Out) {
  if (!Expr)
    return;
  if (Expr->K == LogicExpr::Var && !Bound.count(Expr->Name))
    Out.insert(Expr->Name);
  const bool Quantifier =
      Expr->K == LogicExpr::Forall || Expr->K == LogicExpr::Exists;
  for (size_t I = 0; I != Expr->Children.size(); ++I) {
    const bool Body = Quantifier && I + 1 == Expr->Children.size();
    const bool Inserted = Body && Bound.insert(Expr->Binder).second;
    freeVariables(Expr->Children[I].get(), Bound, Out);
    if (Inserted)
      Bound.erase(Expr->Binder);
  }
}

std::set<std::string> freeVariables(const LogicExpr *Expr) {
  std::set<std::string> Bound, Out;
  freeVariables(Expr, Bound, Out);
  return Out;
}

/// Names no term of the module uses.
class FreshNames {
  std::set<std::string> Used;

public:
  explicit FreshNames(const ObligationModule &Module) {
    for (const Obligation &Item : Module.Obligations)
      logicNames(Item.Goal.get(), Used);
    for (const auto *Functions :
         {&Module.LogicFunctions, &Module.EvidenceFunctions})
      for (const auto &[Identity, Function] : *Functions) {
        (void)Identity;
        logicNames(Function.StepDefinition.get(), Used);
        for (const auto &Parameter : Function.Parameters)
          Used.insert(Parameter.Name);
        for (const auto &Decrease : Function.Decreases)
          logicNames(Decrease.get(), Used);
      }
  }
  std::string make(const std::string &Base) {
    std::string Name = "__induction." + Base;
    for (unsigned I = 1; Used.count(Name); ++I)
      Name = "__induction." + Base + "." + std::to_string(I);
    Used.insert(Name);
    return Name;
  }
};

/// \p Expr with each free variable in \p Map replaced, simultaneously; a
/// binder is renamed apart where a replacement mentions its name.
std::unique_ptr<LogicExpr>
substitute(const LogicExpr *Expr,
           const std::map<std::string, const LogicExpr *> &Map,
           FreshNames &Fresh) {
  if (!Expr)
    return nullptr;
  if (Expr->K == LogicExpr::Var)
    if (auto It = Map.find(Expr->Name); It != Map.end())
      return cloneLogicExpr(It->second);
  auto Copy = cloneLogicExpr(Expr);
  Copy->Children.clear();
  Copy->Patterns.clear();
  const bool Quantifier =
      Expr->K == LogicExpr::Forall || Expr->K == LogicExpr::Exists;
  if (!Quantifier) {
    for (const auto &Child : Expr->Children)
      Copy->Children.push_back(substitute(Child.get(), Map, Fresh));
    return Copy;
  }
  // The bounds lie outside the binder's scope; the body and patterns inside.
  std::map<std::string, const LogicExpr *> Inner = Map;
  Inner.erase(Expr->Binder);
  std::set<std::string> Mentioned;
  for (const auto &[Name, Value] : Inner) {
    (void)Name;
    std::set<std::string> Names = freeVariables(Value);
    Mentioned.insert(Names.begin(), Names.end());
  }
  std::unique_ptr<LogicExpr> Renamed;
  if (Mentioned.count(Expr->Binder)) {
    Copy->Binder = Fresh.make(Expr->Binder);
    Renamed = node(LogicExpr::Var, LogicSort::mathematicalInteger(), Expr);
    Renamed->Name = Copy->Binder;
    // The binder's own occurrences keep their sort.
    std::function<const LogicExpr *(const LogicExpr *)> occurrence =
        [&](const LogicExpr *E) -> const LogicExpr * {
      if (!E)
        return nullptr;
      if (E->K == LogicExpr::Var && E->Name == Expr->Binder)
        return E;
      for (const auto &Child : E->Children)
        if (const LogicExpr *Found = occurrence(Child.get()))
          return Found;
      return nullptr;
    };
    if (const LogicExpr *Occurrence = occurrence(Expr->Children.back().get()))
      Renamed->Sort = Occurrence->Sort;
    Inner[Expr->Binder] = Renamed.get();
  }
  for (size_t I = 0; I != Expr->Children.size(); ++I)
    Copy->Children.push_back(
        substitute(Expr->Children[I].get(),
                   I + 1 == Expr->Children.size() ? Inner : Map, Fresh));
  for (const auto &Pattern : Expr->Patterns)
    Copy->Patterns.push_back(substitute(Pattern.get(), Inner, Fresh));
  return Copy;
}

std::unique_ptr<LogicExpr> substitute(const LogicExpr *Expr,
                                      const std::string &Name,
                                      const LogicExpr &Value,
                                      FreshNames &Fresh) {
  return substitute(Expr, {{Name, &Value}}, Fresh);
}

/// The goal without the disjuncts that assume a theorem: an obligation's
/// goal is !A1 || ... || !An || C, and dropping !T for a theorem T leaves
/// the function's own claim.
std::unique_ptr<LogicExpr>
withoutTheorems(const LogicExpr *Goal, const std::set<std::string> &Theorems,
                const std::set<std::string> &Negated) {
  if (!Goal || Goal->K != LogicExpr::Or)
    return cloneLogicExpr(Goal);
  std::vector<std::unique_ptr<LogicExpr>> Kept;
  for (const auto &Child : Goal->Children) {
    const LogicExpr *C = Child.get();
    if (C->K == LogicExpr::Not && C->Children.size() == 1 &&
        Theorems.count(logicKey(C->Children.front().get())))
      continue;
    // A theorem that is itself a negation appears unnegated once double
    // negation is simplified.
    if (Negated.count(logicKey(C)))
      continue;
    if (C->K == LogicExpr::Or) {
      Kept.push_back(withoutTheorems(C, Theorems, Negated));
      continue;
    }
    Kept.push_back(cloneLogicExpr(C));
  }
  if (Kept.empty())
    return boolConstant(false);
  return junction(LogicExpr::Or, std::move(Kept));
}

bool unwinding(const Obligation &Item) {
  return Item.Kind == ObligationKind::Unwinding;
}

/// The claim's counterexample: some obligation other than an unwinding one
/// fails, without the theorems the module added.
std::unique_ptr<LogicExpr> claimCounterexample(const ObligationModule &Module) {
  std::set<std::string> Theorems, Negated;
  for (const auto &Theorem : Module.Theorems) {
    Theorems.insert(logicKey(Theorem.get()));
    if (Theorem->K == LogicExpr::Not && Theorem->Children.size() == 1)
      Negated.insert(logicKey(Theorem->Children.front().get()));
  }
  std::vector<std::unique_ptr<LogicExpr>> Failures;
  for (const Obligation &Item : Module.Obligations)
    if (!unwinding(Item))
      Failures.push_back(
          logicNot(withoutTheorems(Item.Goal.get(), Theorems, Negated)));
  if (Failures.empty())
    return nullptr;
  return junction(LogicExpr::Or, std::move(Failures));
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
definitionIn(const LogicExpr *Expr, const std::set<std::string> &Keep,
             const std::set<std::string> &Binders) {
  if (!Expr || Expr->K != LogicExpr::Eq || Expr->Children.size() != 2)
    return std::nullopt;
  for (unsigned Side : {0U, 1U}) {
    const LogicExpr *Var = Expr->Children[Side].get();
    const LogicExpr *Value = Expr->Children[1 - Side].get();
    if (Var->K != LogicExpr::Var || Keep.count(Var->Name) ||
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
/// weaker there, so the result has a model whenever \p Expr has, and a
/// model of it gives one of \p Expr with x := t. The induction variables in
/// \p Keep stay.
std::unique_ptr<LogicExpr> eliminateDefinitions(
    const LogicExpr *Expr, bool Antitone, const std::set<std::string> &Keep,
    const std::set<std::string> &Binders, unsigned &Budget, FreshNames &Fresh) {
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
        std::vector<std::unique_ptr<LogicExpr>> Rest;
        for (unsigned K = 0; K != Conjuncts.size(); ++K)
          if (K != J)
            Rest.push_back(cloneLogicExpr(Conjuncts[K]));
        auto Rewritten = node(LogicExpr::Or, LogicSort::boolSort(), Expr);
        for (unsigned K = 0; K != Expr->Children.size(); ++K)
          Rewritten->Children.push_back(
              K != I ? cloneLogicExpr(Expr->Children[K].get())
                     : logicNot(junction(LogicExpr::And, std::move(Rest))));
        auto Substituted = substitute(Rewritten.get(), Definition->first,
                                      *Definition->second, Fresh);
        return eliminateDefinitions(Substituted.get(), Antitone, Keep, Binders,
                                    Budget, Fresh);
      }
    }
  }
  auto Copy = cloneLogicExpr(Expr);
  Copy->Children.clear();
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
        Budget, Fresh));
  }
  return Copy;
}

void collectBinders(const LogicExpr *Expr, std::set<std::string> &Binders) {
  if (!Expr)
    return;
  if (Expr->K == LogicExpr::Forall || Expr->K == LogicExpr::Exists)
    Binders.insert(Expr->Binder);
  for (const auto &Child : Expr->Children)
    collectBinders(Child.get(), Binders);
}

const LogicFunctionDecl *functionOf(const ObligationModule &Module,
                                    const std::string &Identity) {
  if (auto It = Module.LogicFunctions.find(Identity);
      It != Module.LogicFunctions.end())
    return &It->second;
  if (auto It = Module.EvidenceFunctions.find(Identity);
      It != Module.EvidenceFunctions.end())
    return &It->second;
  return nullptr;
}

void calledFunctions(const LogicExpr *Expr, std::set<std::string> &Out) {
  if (!Expr)
    return;
  if (Expr->K == LogicExpr::SpecCall)
    Out.insert(Expr->SpecCallee);
  for (const auto &Child : Expr->Children)
    calledFunctions(Child.get(), Out);
}

/// The functions that reach \p Identity through step definitions and are
/// reached from it: its recursion group, itself included when recursive.
std::set<std::string> recursionGroup(const ObligationModule &Module,
                                     const std::string &Identity) {
  auto reach = [&](const std::string &From) {
    std::set<std::string> Seen;
    std::vector<std::string> Work{From};
    while (!Work.empty()) {
      std::string Next = std::move(Work.back());
      Work.pop_back();
      const LogicFunctionDecl *Function = functionOf(Module, Next);
      if (!Function)
        continue;
      std::set<std::string> Callees;
      calledFunctions(Function->StepDefinition.get(), Callees);
      for (const std::string &Callee : Callees)
        if (Seen.insert(Callee).second)
          Work.push_back(Callee);
    }
    return Seen;
  };
  std::set<std::string> Group;
  for (const std::string &Member : reach(Identity))
    if (reach(Member).count(Identity))
      Group.insert(Member);
  return Group;
}

/// The variable an argument is, possibly seen through a conversion into
/// the parameter's sort, and how to turn a parameter value back into it.
struct ArgumentVariable {
  std::string Name;
  LogicSort Sort;
  bool ThroughBvToInt = false;
};

std::optional<ArgumentVariable>
argumentVariable(const LogicExpr *Argument,
                 const std::set<std::string> &Bound) {
  if (Argument->K == LogicExpr::Var && !Bound.count(Argument->Name))
    return ArgumentVariable{Argument->Name, Argument->Sort, false};
  if (Argument->K == LogicExpr::BvToInt && Argument->Children.size() == 1 &&
      Argument->Children.front()->K == LogicExpr::Var &&
      !Bound.count(Argument->Children.front()->Name))
    return ArgumentVariable{Argument->Children.front()->Name,
                            Argument->Children.front()->Sort, true};
  return std::nullopt;
}

/// The variable's value that makes its argument \p Target.
std::unique_ptr<LogicExpr> variableValue(const ArgumentVariable &Variable,
                                         const LogicExpr &Target) {
  if (!Variable.ThroughBvToInt)
    return cloneLogicExpr(&Target);
  auto Converted = node(LogicExpr::IntToBv, Variable.Sort, &Target);
  Converted->Children.push_back(cloneLogicExpr(&Target));
  return Converted;
}

/// Collects the recursive applications of a scheme's function along a
/// definition, with the condition and binders under which each is reached.
class RecursionWalk {
  const ObligationModule &Module;
  const std::string &Function;
  const std::set<std::string> &Group;
  const std::vector<ArgumentVariable> &Variables;
  FreshNames &Fresh;

public:
  std::vector<InductionInstance> Instances;

  RecursionWalk(const ObligationModule &Module, const std::string &Function,
                const std::set<std::string> &Group,
                const std::vector<ArgumentVariable> &Variables,
                FreshNames &Fresh)
      : Module(Module), Function(Function), Group(Group), Variables(Variables),
        Fresh(Fresh) {}

  /// The step definition of \p Callee at \p Arguments.
  std::unique_ptr<LogicExpr>
  stepAt(const LogicFunctionDecl &Callee,
         const std::vector<const LogicExpr *> &Arguments) {
    if (!Callee.StepDefinition || Arguments.size() != Callee.Parameters.size())
      return nullptr;
    std::map<std::string, const LogicExpr *> Map;
    for (size_t I = 0; I != Arguments.size(); ++I)
      Map[Callee.Parameters[I].Name] = Arguments[I];
    return substitute(Callee.StepDefinition.get(), Map, Fresh);
  }

  void walk(const LogicExpr *E, std::vector<const LogicExpr *> &Path,
            std::vector<InductionInstance::Binder *> &Binders,
            std::vector<std::unique_ptr<InductionInstance::Binder>> &Owned,
            unsigned Depth) {
    if (!E || Instances.size() >= MaxInstances)
      return;
    switch (E->K) {
    case LogicExpr::Ite: {
      walk(E->Children[0].get(), Path, Binders, Owned, Depth);
      Path.push_back(E->Children[0].get());
      walk(E->Children[1].get(), Path, Binders, Owned, Depth);
      Path.pop_back();
      auto Else = logicNot(cloneLogicExpr(E->Children[0].get()));
      Path.push_back(Else.get());
      walk(E->Children[2].get(), Path, Binders, Owned, Depth);
      Path.pop_back();
      Retained.push_back(std::move(Else));
      return;
    }
    case LogicExpr::And:
    case LogicExpr::Or: {
      // Each operand is evaluated once the earlier ones did not decide.
      const size_t Mark = Path.size();
      for (const auto &Child : E->Children) {
        walk(Child.get(), Path, Binders, Owned, Depth);
        if (E->K == LogicExpr::And) {
          Path.push_back(Child.get());
        } else {
          auto Not = logicNot(cloneLogicExpr(Child.get()));
          Path.push_back(Not.get());
          Retained.push_back(std::move(Not));
        }
      }
      Path.resize(Mark);
      return;
    }
    case LogicExpr::Forall:
    case LogicExpr::Exists: {
      const bool Bounded = E->Children.size() == 3;
      if (Bounded) {
        walk(E->Children[0].get(), Path, Binders, Owned, Depth);
        walk(E->Children[1].get(), Path, Binders, Owned, Depth);
      }
      auto Binder = std::make_unique<InductionInstance::Binder>();
      Binder->Name = Fresh.make(E->Binder);
      if (Bounded) {
        Binder->Lo = cloneLogicExpr(E->Children[0].get());
        Binder->Hi = cloneLogicExpr(E->Children[1].get());
      }
      std::vector<std::pair<std::string, LogicSort>> Occurrences;
      std::set<std::string> None;
      logicFreeVariables(E->Children.back().get(), None, Occurrences);
      auto Renamed = node(LogicExpr::Var, LogicSort::mathematicalInteger(), E);
      Renamed->Name = Binder->Name;
      for (const auto &[Name, Sort] : Occurrences)
        if (Name == E->Binder)
          Renamed->Sort = Sort;
      std::unique_ptr<LogicExpr> Body =
          substitute(E->Children.back().get(), E->Binder, *Renamed, Fresh);
      Binders.push_back(Binder.get());
      Owned.push_back(std::move(Binder));
      walk(Body.get(), Path, Binders, Owned, Depth);
      Binders.pop_back();
      Retained.push_back(std::move(Body));
      return;
    }
    case LogicExpr::SpecCall: {
      for (const auto &Child : E->Children)
        walk(Child.get(), Path, Binders, Owned, Depth);
      if (E->SpecCallee == Function) {
        record(*E, Path, Binders);
        return;
      }
      if (!Group.count(E->SpecCallee) || Depth >= MaxGroupUnfolding)
        return;
      const LogicFunctionDecl *Callee = functionOf(Module, E->SpecCallee);
      if (!Callee)
        return;
      std::vector<const LogicExpr *> Arguments;
      for (const auto &Child : E->Children)
        Arguments.push_back(Child.get());
      std::unique_ptr<LogicExpr> Body = stepAt(*Callee, Arguments);
      if (!Body)
        return;
      walk(Body.get(), Path, Binders, Owned, Depth + 1);
      Retained.push_back(std::move(Body));
      return;
    }
    default:
      for (const auto &Child : E->Children)
        walk(Child.get(), Path, Binders, Owned, Depth);
      return;
    }
  }

private:
  std::vector<std::unique_ptr<LogicExpr>> Retained;

  void record(const LogicExpr &Call, const std::vector<const LogicExpr *> &Path,
              const std::vector<InductionInstance::Binder *> &Binders) {
    if (Call.Children.size() != Variables.size())
      return;
    InductionInstance Instance;
    for (const InductionInstance::Binder *Binder : Binders) {
      InductionInstance::Binder Copy;
      Copy.Name = Binder->Name;
      Copy.Lo = cloneLogicExpr(Binder->Lo.get());
      Copy.Hi = cloneLogicExpr(Binder->Hi.get());
      Instance.Binders.push_back(std::move(Copy));
    }
    std::vector<std::unique_ptr<LogicExpr>> Conditions;
    for (const LogicExpr *Condition : Path)
      Conditions.push_back(cloneLogicExpr(Condition));
    Instance.Guard = junction(LogicExpr::And, std::move(Conditions));
    for (size_t I = 0; I != Variables.size(); ++I)
      Instance.Values.push_back(variableValue(Variables[I], *Call.Children[I]));
    Instances.push_back(std::move(Instance));
  }
};

std::string displayName(const ObligationModule &Module,
                        const std::string &Variable) {
  if (auto It = Module.DiagnosticVariables.find(Variable);
      It != Module.DiagnosticVariables.end())
    return It->second.DisplayName;
  return Variable;
}

/// The applications of recursive functions in \p Expr outside quantifiers,
/// in order of first appearance.
void recursiveApplications(const ObligationModule &Module,
                           const LogicExpr *Expr,
                           std::vector<const LogicExpr *> &Out) {
  if (!Expr || Expr->K == LogicExpr::Forall || Expr->K == LogicExpr::Exists)
    return;
  for (const auto &Child : Expr->Children)
    recursiveApplications(Module, Child.get(), Out);
  if (Expr->K != LogicExpr::SpecCall)
    return;
  const LogicFunctionDecl *Function = functionOf(Module, Expr->SpecCallee);
  if (Function && !Function->Decreases.empty() &&
      Function->Decreases.size() <= 8)
    Out.push_back(Expr);
}

void integerArgumentVariables(
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
    integerArgumentVariables(Child.get(),
                             InArgument || Expr->K == LogicExpr::SpecCall,
                             Bound, Seen, Out);
  if (Inserted)
    Bound.erase(Expr->Binder);
}

bool integerSort(const LogicSort &Sort) {
  return Sort.Kind == LogicSortKind::MathematicalInteger ||
         Sort.Kind == LogicSortKind::BitVector;
}

LogicFunctionDecl copyFunction(const LogicFunctionDecl &Function) {
  LogicFunctionDecl Copy;
  Copy.Identity = Function.Identity;
  Copy.DisplayName = Function.DisplayName;
  Copy.Parameters = Function.Parameters;
  Copy.ResultSort = Function.ResultSort;
  Copy.DefinitionFuel = Function.DefinitionFuel;
  Copy.StepDefinition = cloneLogicExpr(Function.StepDefinition.get());
  for (const auto &Definition : Function.DefinitionLevels)
    Copy.DefinitionLevels.push_back(cloneLogicExpr(Definition.get()));
  Copy.Choice = Function.Choice;
  Copy.Unfolding = cloneLogicExpr(Function.Unfolding.get());
  for (const auto &Post : Function.Postconditions)
    Copy.Postconditions.push_back(cloneLogicExpr(Post.get()));
  for (const auto &Decrease : Function.Decreases)
    Copy.Decreases.push_back(cloneLogicExpr(Decrease.get()));
  return Copy;
}

} // namespace

std::unique_ptr<LogicExpr>
substituteFree(const ObligationModule &Module, const LogicExpr *Expr,
               const std::map<std::string, const LogicExpr *> &Map) {
  FreshNames Fresh(Module);
  return substitute(Expr, Map, Fresh);
}

ObligationModule copyObligationModule(const ObligationModule &Module) {
  ObligationModule Copy;
  Copy.FunctionName = Module.FunctionName;
  Copy.FunctionIdentity = Module.FunctionIdentity;
  Copy.CorrectnessGoal = cloneLogicExpr(Module.CorrectnessGoal.get());
  Copy.CounterexampleQuery = cloneLogicExpr(Module.CounterexampleQuery.get());
  for (const Obligation &Item : Module.Obligations) {
    Obligation Same;
    Same.Id = Item.Id;
    Same.StableId = Item.StableId;
    Same.Kind = Item.Kind;
    Same.Loc = Item.Loc;
    Same.EndLoc = Item.EndLoc;
    Same.Source = Item.Source;
    Same.TraceEventCount = Item.TraceEventCount;
    Same.Note = Item.Note;
    Same.Goal = cloneLogicExpr(Item.Goal.get());
    Same.CounterexampleQuery = cloneLogicExpr(Item.CounterexampleQuery.get());
    Copy.Obligations.push_back(std::move(Same));
  }
  Copy.DiagnosticVariables = Module.DiagnosticVariables;
  for (const DiagnosticTraceEvent &Event : Module.TraceEvents) {
    DiagnosticTraceEvent Same;
    Same.Kind = Event.Kind;
    Same.Message = Event.Message;
    Same.Loc = Event.Loc;
    Same.EndLoc = Event.EndLoc;
    Same.Source = Event.Source;
    Same.Guard = cloneLogicExpr(Event.Guard.get());
    for (const DiagnosticTraceValue &Value : Event.Values)
      Same.Values.push_back({Value.Label, cloneLogicExpr(Value.Value.get())});
    Copy.TraceEvents.push_back(std::move(Same));
  }
  for (const auto &[Identity, Function] : Module.LogicFunctions)
    Copy.LogicFunctions.emplace(Identity, copyFunction(Function));
  for (const auto &[Identity, Function] : Module.EvidenceFunctions)
    Copy.EvidenceFunctions.emplace(Identity, copyFunction(Function));
  Copy.RequiredFeatures = Module.RequiredFeatures;
  Copy.ResultVarName = Module.ResultVarName;
  Copy.HeapPrefix = Module.HeapPrefix;
  Copy.BMCTransform = Module.BMCTransform;
  Copy.AssumedPosts = Module.AssumedPosts;
  Copy.AssumedUnfoldings = Module.AssumedUnfoldings;
  Copy.InductivePosts = Module.InductivePosts;
  Copy.Given = Module.Given;
  Copy.Undecided = Module.Undecided;
  Copy.Contract = Module.Contract;
  for (const auto &Theorem : Module.Theorems)
    Copy.Theorems.push_back(cloneLogicExpr(Theorem.get()));
  for (const auto &Precondition : Module.Preconditions)
    Copy.Preconditions.push_back(cloneLogicExpr(Precondition.get()));
  Copy.Attempt = Module.Attempt;
  return Copy;
}

std::vector<InductionScheme> inductionSchemes(const ObligationModule &Module) {
  std::vector<InductionScheme> Schemes;
  std::unique_ptr<LogicExpr> Claim = claimCounterexample(Module);
  if (!Claim)
    return Schemes;
  FreshNames Fresh(Module);
  std::set<std::string> Binders;
  collectBinders(Claim.get(), Binders);

  // By the measure of each recursive spec the claim applies.
  std::vector<const LogicExpr *> Applications;
  recursiveApplications(Module, Claim.get(), Applications);
  std::set<std::string> Seen;
  for (const LogicExpr *Application : Applications) {
    if (Schemes.size() == MaxFunctionSchemes)
      break;
    const LogicFunctionDecl *Function =
        functionOf(Module, Application->SpecCallee);
    if (!Function ||
        Application->Children.size() != Function->Parameters.size())
      continue;
    std::vector<std::pair<std::string, LogicSort>> Free;
    std::set<std::string> Outside = Binders;
    logicFreeVariables(Application, Outside, Free);
    std::set<std::string> Variables;
    for (const auto &[Name, Sort] : Free)
      if (Sort.Kind != LogicSortKind::Heap)
        Variables.insert(Name);
    if (Variables.empty())
      continue;
    std::string Key = Function->Identity;
    for (const std::string &Name : Variables)
      Key += "\x1f" + Name;
    if (!Seen.insert(Key).second)
      continue;

    InductionScheme Scheme;
    Scheme.Function = Function->Identity;
    Scheme.Description = "following " + Function->DisplayName;
    std::map<std::string, const LogicExpr *> Arguments;
    for (size_t I = 0; I != Function->Parameters.size(); ++I)
      Arguments[Function->Parameters[I].Name] = Application->Children[I].get();
    for (const auto &Decrease : Function->Decreases)
      Scheme.Measure.push_back(substitute(Decrease.get(), Arguments, Fresh));

    // The variables the application's arguments are, if every argument is
    // one (or a heap, which stays): then the recursion's own applications
    // give instances.
    std::vector<ArgumentVariable> ByArgument;
    bool Invertible = true;
    std::set<std::string> Distinct;
    for (const auto &Argument : Application->Children) {
      if (Argument->Sort.Kind == LogicSortKind::Heap) {
        ByArgument.push_back({});
        continue;
      }
      std::optional<ArgumentVariable> Variable =
          argumentVariable(Argument.get(), Binders);
      if (!Variable || !Distinct.insert(Variable->Name).second) {
        Invertible = false;
        break;
      }
      ByArgument.push_back(*Variable);
    }
    if (Invertible && Distinct == Variables) {
      for (const ArgumentVariable &Variable : ByArgument)
        if (!Variable.Name.empty())
          Scheme.Variables.emplace_back(Variable.Name, Variable.Sort);
      std::set<std::string> Group = recursionGroup(Module, Function->Identity);
      RecursionWalk Walk(Module, Function->Identity, Group, ByArgument, Fresh);
      std::vector<const LogicExpr *> Self;
      for (const auto &Argument : Application->Children)
        Self.push_back(Argument.get());
      if (std::unique_ptr<LogicExpr> Body = Walk.stepAt(*Function, Self)) {
        std::vector<const LogicExpr *> Path;
        std::vector<InductionInstance::Binder *> Open;
        std::vector<std::unique_ptr<InductionInstance::Binder>> Owned;
        Walk.walk(Body.get(), Path, Open, Owned, 0);
      }
      // A heap argument maps to itself.
      for (InductionInstance &Instance : Walk.Instances) {
        std::vector<std::unique_ptr<LogicExpr>> Values;
        for (size_t I = 0; I != ByArgument.size(); ++I)
          if (!ByArgument[I].Name.empty())
            Values.push_back(std::move(Instance.Values[I]));
        Instance.Values = std::move(Values);
        Scheme.Instances.push_back(std::move(Instance));
      }
    } else {
      // The whole hypothesis alone, over the arguments' integer variables.
      for (const auto &[Name, Sort] : Free)
        if (Variables.count(Name))
          Scheme.Variables.emplace_back(Name, Sort);
      if (!llvm::all_of(Scheme.Variables, [](const auto &Variable) {
            return integerSort(Variable.second);
          }))
        continue;
    }
    Schemes.push_back(std::move(Scheme));
  }

  // By one integer variable in an application's arguments: strong induction
  // on its value.
  std::vector<std::pair<std::string, LogicSort>> Integers;
  std::set<std::string> Bound, Found;
  integerArgumentVariables(Claim.get(), false, Bound, Found, Integers);
  unsigned Added = 0;
  for (const auto &[Name, Sort] : Integers) {
    if (Added == MaxVariableSchemes)
      break;
    ++Added;
    InductionScheme Scheme;
    Scheme.Description = "on " + displayName(Module, Name);
    Scheme.Variables.emplace_back(Name, Sort);
    auto Variable = node(LogicExpr::Var, Sort);
    Variable->Name = Name;
    Scheme.Measure.push_back(asMath(std::move(Variable)));
    Schemes.push_back(std::move(Scheme));
  }
  return Schemes;
}

llvm::Expected<ObligationModule>
inductionModule(const ObligationModule &Module, const InductionScheme &Scheme) {
  std::unique_ptr<LogicExpr> Claim = claimCounterexample(Module);
  if (!Claim || Scheme.Variables.empty() || Scheme.Measure.empty())
    return llvm::createStringError(llvm::inconvertibleErrorCode(),
                                   "no induction over this module");
  FreshNames Fresh(Module);
  std::set<std::string> Binders, Keep;
  collectBinders(Claim.get(), Binders);
  for (const auto &[Name, Sort] : Scheme.Variables) {
    (void)Sort;
    Keep.insert(Name);
  }
  // The claim with the definitions it assumes substituted has a model
  // whenever the claim has, and only then is the hypothesis about the
  // variables themselves.
  unsigned Budget = 256;
  std::unique_ptr<LogicExpr> Counterexample =
      eliminateDefinitions(Claim.get(), false, Keep, Binders, Budget, Fresh);
  if (logicNodeCount(Counterexample.get()) >
      4 * logicNodeCount(Claim.get()) + 10000)
    Counterexample = std::move(Claim);

  // The claim at Values: no counterexample there, with the theorems that
  // mention the variables restated there (they hold at every value).
  auto claimAt = [&](const std::vector<const LogicExpr *> &Values) {
    std::map<std::string, const LogicExpr *> Map;
    for (size_t I = 0; I != Scheme.Variables.size(); ++I)
      Map[Scheme.Variables[I].first] = Values[I];
    std::vector<std::unique_ptr<LogicExpr>> Parts;
    Parts.push_back(logicNot(substitute(Counterexample.get(), Map, Fresh)));
    return junction(LogicExpr::And, std::move(Parts));
  };
  auto theoremsAt = [&](const std::vector<const LogicExpr *> &Values) {
    std::map<std::string, const LogicExpr *> Map;
    for (size_t I = 0; I != Scheme.Variables.size(); ++I)
      Map[Scheme.Variables[I].first] = Values[I];
    std::vector<std::unique_ptr<LogicExpr>> Parts;
    for (const auto &Theorem : Module.Theorems)
      if (mentionsAny(Theorem.get(), Keep))
        Parts.push_back(substitute(Theorem.get(), Map, Fresh));
    return junction(LogicExpr::And, std::move(Parts));
  };
  auto measureAt = [&](const std::vector<const LogicExpr *> &Values) {
    std::map<std::string, const LogicExpr *> Map;
    for (size_t I = 0; I != Scheme.Variables.size(); ++I)
      Map[Scheme.Variables[I].first] = Values[I];
    std::vector<std::unique_ptr<LogicExpr>> Measure;
    for (const auto &Component : Scheme.Measure)
      Measure.push_back(substitute(Component.get(), Map, Fresh));
    return Measure;
  };
  auto quantify = [&](std::unique_ptr<LogicExpr> Body,
                      const std::vector<InductionInstance::Binder> &Over) {
    for (auto It = Over.rbegin(); It != Over.rend(); ++It) {
      auto Quantifier = node(LogicExpr::Forall, LogicSort::boolSort());
      Quantifier->Binder = It->Name;
      if (It->Lo && It->Hi) {
        Quantifier->Children.push_back(cloneLogicExpr(It->Lo.get()));
        Quantifier->Children.push_back(cloneLogicExpr(It->Hi.get()));
      }
      Quantifier->Children.push_back(std::move(Body));
      Body = std::move(Quantifier);
    }
    return Body;
  };

  std::vector<std::unique_ptr<LogicExpr>> Hypothesis;
  for (const InductionInstance &Instance : Scheme.Instances) {
    std::vector<const LogicExpr *> Values;
    for (const auto &Value : Instance.Values)
      Values.push_back(Value.get());
    if (Values.size() != Scheme.Variables.size())
      continue;
    auto Smaller = decrease(measureAt(Values), Scheme.Measure);
    auto Premise =
        both(cloneLogicExpr(Instance.Guard.get()), std::move(Smaller));
    auto Step =
        both(theoremsAt(Values), implies(std::move(Premise), claimAt(Values)));
    Hypothesis.push_back(quantify(std::move(Step), Instance.Binders));
  }
  // The whole hypothesis, where the variables are integers: the claim at
  // every smaller value.
  if (llvm::all_of(Scheme.Variables, [](const auto &Variable) {
        return integerSort(Variable.second);
      })) {
    std::vector<InductionInstance::Binder> Over;
    std::vector<std::unique_ptr<LogicExpr>> Owned;
    std::vector<const LogicExpr *> Values;
    for (const auto &[Name, Sort] : Scheme.Variables) {
      InductionInstance::Binder Binder;
      Binder.Name = Fresh.make(displayName(Module, Name));
      auto Bound = node(LogicExpr::Var, LogicSort::mathematicalInteger());
      Bound->Name = Binder.Name;
      if (Sort.Kind == LogicSortKind::BitVector) {
        auto Converted = node(LogicExpr::IntToBv, Sort);
        Converted->Children.push_back(std::move(Bound));
        Bound = std::move(Converted);
      }
      Values.push_back(Bound.get());
      Owned.push_back(std::move(Bound));
      Over.push_back(std::move(Binder));
    }
    auto Smaller = decrease(measureAt(Values), Scheme.Measure);
    Hypothesis.push_back(
        quantify(implies(std::move(Smaller), claimAt(Values)), Over));
  }
  if (Hypothesis.empty())
    return llvm::createStringError(llvm::inconvertibleErrorCode(),
                                   "the induction has no hypothesis");
  std::unique_ptr<LogicExpr> Assumed =
      junction(LogicExpr::And, std::move(Hypothesis));

  ObligationModule Result = copyObligationModule(Module);
  for (Obligation &Item : Result.Obligations) {
    if (unwinding(Item))
      continue;
    Item.Goal = implies(cloneLogicExpr(Assumed.get()), std::move(Item.Goal));
    Item.CounterexampleQuery = logicNot(cloneLogicExpr(Item.Goal.get()));
  }
  Result.CorrectnessGoal = logicCompleteGoal(Result.Obligations);
  Result.CounterexampleQuery =
      logicNot(cloneLogicExpr(Result.CorrectnessGoal.get()));
  // Functions a measure applies may only have been kept as evidence.
  std::set<std::string> Called;
  calledFunctions(Assumed.get(), Called);
  for (size_t I = 0; I != Called.size(); ++I) {
    std::set<std::string> More;
    for (const std::string &Identity : Called) {
      if (Result.LogicFunctions.count(Identity))
        continue;
      auto It = Result.EvidenceFunctions.find(Identity);
      if (It == Result.EvidenceFunctions.end())
        return llvm::createStringError(llvm::inconvertibleErrorCode(),
                                       "the induction needs an undeclared "
                                       "function");
      calledFunctions(It->second.StepDefinition.get(), More);
      for (const auto &Definition : It->second.DefinitionLevels)
        calledFunctions(Definition.get(), More);
      Result.LogicFunctions.emplace(Identity, copyFunction(It->second));
    }
    Called.insert(More.begin(), More.end());
  }
  Result.Attempt = ModuleAttempt::Induction;
  auto Features = validateObligationModule(Result);
  if (!Features)
    return Features.takeError();
  Result.RequiredFeatures = *Features;
  return std::move(Result);
}

} // namespace verify
} // namespace clang
