//===- unittests/Verify/ObligationValidationTest.cpp ----------------------===//
//
// Validation of modules whose roots share terms, as built modules do: a
// shared term is checked once, and each root still gets every check.
//
//===----------------------------------------------------------------------===//

#include "Backend/Obligation.h"
#include "llvm/Support/Error.h"
#include "gtest/gtest.h"
#include <chrono>

using namespace clang::verify;

namespace {

LogicSort math() { return LogicSort::mathematicalInteger(); }
LogicSort bv32() { return LogicSort::bitVector(32, true); }

LogicExprRef term(LogicExpr::Kind Kind, LogicSort Sort,
                  std::vector<LogicExprRef> Children = {}) {
  auto E = std::make_unique<LogicExpr>(Kind);
  E->Sort = Sort;
  E->Children = std::move(Children);
  return LogicExprRef(std::move(E));
}

LogicExprRef variable(llvm::StringRef Name, LogicSort Sort) {
  auto E = std::make_unique<LogicExpr>(LogicExpr::Var);
  E->Sort = Sort;
  E->Name = Name.str();
  return LogicExprRef(std::move(E));
}

LogicExprRef zero(LogicSort Sort) { return term(LogicExpr::IntLit, Sort); }

LogicExprRef equal(LogicExprRef Left, LogicExprRef Right) {
  return term(LogicExpr::Eq, LogicSort::boolSort(), {Left, Right});
}

LogicExprRef forall(llvm::StringRef Binder, LogicExprRef Body) {
  auto E = std::make_unique<LogicExpr>(LogicExpr::Forall);
  E->Sort = LogicSort::boolSort();
  E->Binder = Binder.str();
  E->Children.push_back(Body);
  return LogicExprRef(std::move(E));
}

std::unique_ptr<LogicExpr> root(const LogicExprRef &Term) {
  return cloneLogicExpr(Term.get());
}

std::unique_ptr<LogicExpr> negation(const LogicExprRef &Term) {
  auto E = std::make_unique<LogicExpr>(LogicExpr::Not);
  E->Sort = LogicSort::boolSort();
  E->Children.push_back(Term);
  return E;
}

/// A module with these goals, in order, and a trace event with these values;
/// every root refers to the terms it is given rather than to copies.
ObligationModule module(std::vector<LogicExprRef> Goals,
                        std::vector<LogicExprRef> TraceValues = {}) {
  ObligationModule M;
  M.FunctionName = "shared";
  M.FunctionIdentity = "shared";
  LogicExprRef Complete;
  for (size_t I = 0; I != Goals.size(); ++I) {
    Obligation Item;
    Item.Id = "o" + std::to_string(I);
    Item.Goal = root(Goals[I]);
    Item.CounterexampleQuery = negation(Goals[I]);
    M.Obligations.push_back(std::move(Item));
    Complete = Complete ? term(LogicExpr::And, LogicSort::boolSort(),
                               {Complete, Goals[I]})
                        : Goals[I];
  }
  M.CorrectnessGoal = root(Complete);
  M.CounterexampleQuery = negation(Complete);
  if (!TraceValues.empty()) {
    DiagnosticTraceEvent Event;
    Event.Guard = root(term(LogicExpr::True, LogicSort::boolSort()));
    for (const LogicExprRef &Value : TraceValues)
      Event.Values.push_back({"value", root(Value)});
    M.TraceEvents.push_back(std::move(Event));
  }
  return M;
}

std::string validationError(const ObligationModule &M) {
  auto Features = validateObligationModule(M);
  if (Features)
    return "";
  return llvm::toString(Features.takeError());
}

TEST(ObligationValidation, SharedTermsKeepEveryFeature) {
  LogicExprRef X = variable("x", math());
  LogicExprRef Y = variable("y", bv32());
  LogicExprRef Quantified = forall("k", equal(variable("k", math()), X));
  LogicExprRef First = term(LogicExpr::Or, LogicSort::boolSort(),
                            {Quantified, equal(X, zero(math()))});
  LogicExprRef Second = term(LogicExpr::Or, LogicSort::boolSort(),
                             {Quantified, equal(Y, zero(bv32()))});
  ObligationModule M = module({First, Second}, {X});
  auto Features = validateObligationModule(M);
  ASSERT_TRUE(static_cast<bool>(Features))
      << llvm::toString(Features.takeError());
  EXPECT_EQ(*Features, logicFeature(LogicFeature::MathematicalIntegers) |
                           logicFeature(LogicFeature::BitVectors) |
                           logicFeature(LogicFeature::Quantifiers));
}

// Each shared term is checked once: this goal's terms double at each of 26
// levels, so a validation that did not share its work would walk 2^26 paths.
TEST(ObligationValidation, SharedTermsAreCheckedOnce) {
  LogicExprRef X = variable("x", math());
  LogicExprRef Term = term(
      LogicExpr::And, LogicSort::boolSort(),
      {forall("k", equal(variable("k", math()), X)), equal(X, zero(math()))});
  for (unsigned Level = 0; Level != 26; ++Level)
    Term = term(LogicExpr::And, LogicSort::boolSort(), {Term, Term});
  const auto Start = std::chrono::steady_clock::now();
  EXPECT_EQ(validationError(module({Term}, {Term})), "");
  EXPECT_LT(std::chrono::duration_cast<std::chrono::milliseconds>(
                std::chrono::steady_clock::now() - Start)
                .count(),
            5000);
}

// The trace value is checked first and has no binder; the goal then binds k
// elsewhere, so the same free k collides with a binder of the goal's root.
TEST(ObligationValidation, BinderOfALaterRootCollidesWithASharedFreeVariable) {
  LogicExprRef K = variable("k", math());
  LogicExprRef Goal =
      term(LogicExpr::Or, LogicSort::boolSort(),
           {forall("k", equal(variable("k", math()), zero(math()))),
            equal(K, zero(math()))});
  EXPECT_EQ(validationError(module({Goal}, {equal(K, zero(math()))})),
            "quantifier binder collides with a free variable");
}

// The same term is bound in the trace value and free in the goal, where its
// sort differs from the variable's.
TEST(ObligationValidation, SharedTermBoundThenFree) {
  LogicExprRef K = variable("k", math());
  ObligationModule M =
      module({equal(K, zero(math()))}, {forall("k", equal(K, zero(math())))});
  M.DiagnosticVariables["k"] = {"k", bv32(), {}, {}, {}};
  EXPECT_EQ(validationError(M), "logical variable has inconsistent sorts: k");
}

// The same machine-integer term is free in the trace value and bound in the
// goal, where a binder must be a mathematical integer.
TEST(ObligationValidation, SharedTermFreeThenBound) {
  LogicExprRef K = variable("k", bv32());
  ObligationModule M =
      module({forall("k", equal(K, zero(bv32())))}, {equal(K, zero(bv32()))});
  EXPECT_EQ(validationError(M),
            "quantifier binder occurrence is not a mathematical integer");
}

// An application shared by two goals is checked against the declarations.
TEST(ObligationValidation, SharedApplicationOfNoDeclaration) {
  auto Call = std::make_unique<LogicExpr>(LogicExpr::SpecCall);
  Call->Sort = math();
  Call->SpecCallee = "g";
  LogicExprRef Application(std::move(Call));
  LogicExprRef Goal = equal(Application, zero(math()));
  EXPECT_EQ(validationError(module({Goal, Goal})),
            "logical application has no owned declaration: g");
}

// A definition's variables are its parameters, not the module's.
TEST(ObligationValidation, DefinitionsHaveTheirOwnVariables) {
  ObligationModule M = module({equal(variable("x", bv32()), zero(bv32()))});
  LogicFunctionDecl F;
  F.Identity = "f";
  F.DisplayName = "f";
  F.Parameters.push_back({"x", math()});
  F.ResultSort = math();
  F.DefinitionFuel = 1;
  F.StepDefinition = root(variable("x", math()));
  F.DefinitionLevels.push_back(root(variable("x", math())));
  M.LogicFunctions["f"] = std::move(F);
  EXPECT_EQ(validationError(M), "");
}

} // namespace
