//===--- Counterexample.cpp -----------------------------------------------===//
#include "Counterexample.h"
#include "../Backend/Certify.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringRef.h"
#include <algorithm>
#include <chrono>
#include <functional>
#include <map>
#include <tuple>

using namespace clang;
using namespace clang::verify;

namespace {
/// An internal name's variable and SSA version: "i_2" is version 2 of "i",
/// "y#2_1" version 1 of the local that shadows y.
std::pair<llvm::StringRef, unsigned> versionOf(llvm::StringRef InternalName) {
  auto [Base, Suffix] = InternalName.rsplit('_');
  unsigned Version = 0;
  if (Base.empty() || Suffix.getAsInteger(10, Version))
    return {InternalName, 0};
  return {Base, Version};
}

std::string valueText(const std::optional<std::string> &Value) {
  return Value.value_or("<unknown>");
}
} // namespace

std::string verify::counterexampleText(const VerifyResult &Result) {
  struct Variable {
    const VerifyModelValue *First;
    std::vector<const VerifyModelValue *> Versions;
  };
  std::vector<Variable> Variables;
  std::map<llvm::StringRef, size_t> IndexOf;
  std::map<std::string, unsigned> Named;
  for (const VerifyModelValue &Value : Result.Model) {
    // A version of a branch the path does not take is no value the variable
    // takes; it equals the one before it there.
    if (Value.OnPath == false)
      continue;
    auto [It, Inserted] = IndexOf.try_emplace(
        versionOf(Value.InternalName).first, Variables.size());
    if (Inserted) {
      Variables.push_back({&Value, {}});
      ++Named[Value.DisplayName];
    }
    Variables[It->second].Versions.push_back(&Value);
  }
  auto position = [](const Variable &V) {
    const ObligationSource &Source = V.First->Source;
    return std::make_tuple(V.First->DisplayName == "result", !Source.isValid(),
                           Source.Line, Source.Column);
  };
  std::stable_sort(Variables.begin(), Variables.end(),
                   [&](const Variable &A, const Variable &B) {
                     return position(A) < position(B);
                   });
  std::string Text;
  for (Variable &V : Variables) {
    std::stable_sort(V.Versions.begin(), V.Versions.end(),
                     [](const VerifyModelValue *A, const VerifyModelValue *B) {
                       return versionOf(A->InternalName).second <
                              versionOf(B->InternalName).second;
                     });
    // A reference's value is the address of what it refers to, which C++
    // writes &r.
    Text += Text.empty() ? "" : ", ";
    Text += (V.First->Reference ? "&" : "") + V.First->DisplayName;
    // Two variables of one name, as a local that shadows another.
    if (Named[V.First->DisplayName] > 1 && V.First->Source.isValid())
      Text += " (line " + std::to_string(V.First->Source.Line) + ")";
    Text += " = ";
    // The values it takes in turn: a version that keeps the value before it,
    // as one that merges branches, adds none.
    const std::optional<std::string> *Previous = nullptr;
    for (const VerifyModelValue *Version : V.Versions) {
      if (Previous && *Previous && *Previous == Version->Value)
        continue;
      Text += (Previous ? " -> " : "") + valueText(Version->Value);
      Previous = &Version->Value;
    }
  }
  return Text;
}

std::string verify::traceStepText(const VerifyTraceEvent &Event) {
  auto value = [&](llvm::StringRef Label) {
    for (const VerifyTraceValue &Value : Event.Values)
      if (Value.Label == Label)
        return valueText(Value.Value);
    return std::string("<unknown>");
  };
  llvm::StringRef Message = Event.Message;
  std::string Text;
  switch (Event.Kind) {
  case DiagnosticTraceKind::Branch:
    Text = Message == "then"   ? "takes the true branch"
           : Message == "else" ? "takes the false branch"
                               : "takes the branch " + Message.str();
    break;
  case DiagnosticTraceKind::Loop:
    if (Message == "entry")
      Text = "enters the loop";
    else if (Message == "inductive iteration")
      Text = "starts an arbitrary iteration of the loop";
    else if (Message == "exit")
      Text = "leaves the loop";
    else if (Message == "break")
      Text = "breaks out of the loop";
    else if (Message == "continue")
      Text = "continues the loop";
    else if (Message.consume_front("iteration "))
      Text = "runs iteration " + Message.str() + " of the loop";
    else if (Message.consume_front("exit after "))
      Text = "leaves the loop after " + Message.str() +
             (Message == "1" ? " iteration" : " iterations");
    else
      Text = "loop: " + Message.str();
    for (const VerifyTraceValue &Value : Event.Values)
      if (Value.Label == "condition")
        Text += ", where its condition is " + valueText(Value.Value);
    break;
  case DiagnosticTraceKind::Call: {
    std::vector<std::string> Arguments;
    for (const VerifyTraceValue &Value : Event.Values)
      Arguments.push_back(valueText(Value.Value));
    Text = "calls " + Message.str() + "(" + llvm::join(Arguments, ", ") + ")";
    break;
  }
  case DiagnosticTraceKind::HeapWrite:
    Text = "stores " + value("value") + " at address " + value("address");
    break;
  case DiagnosticTraceKind::Allocation:
    Text = (Message == "automatic allocation"
                ? "creates a local object at address "
                : "allocates an object at address ") +
           value("address");
    break;
  case DiagnosticTraceKind::LifetimeEnd:
    Text = "ends the lifetime of a local object";
    break;
  case DiagnosticTraceKind::Deallocation:
    Text = "deletes the object at address " + value("address");
    break;
  case DiagnosticTraceKind::Return:
    Text = Event.Values.empty() ? "returns" : "returns " + value("value");
    break;
  }
  if (!Event.Active)
    Text = "perhaps " + Text +
           " (the counterexample does not decide whether "
           "this step is taken)";
  return Text;
}

namespace {
/// The values a counterexample gives the variables of its obligation's goal;
/// a logical function is evaluated by its definition.
class AssignedValues : public CandidateModel {
  const CounterexampleAssignment &Assignment;

public:
  explicit AssignedValues(const CounterexampleAssignment &Assignment)
      : Assignment(Assignment) {}
  std::optional<LogicValue> constant(const std::string &Name,
                                     const LogicSort &) override {
    auto It = Assignment.Values.find(Name);
    if (It == Assignment.Values.end())
      return std::nullopt;
    return It->second;
  }
  std::optional<bool> validPointer(const CertInt &) override {
    return std::nullopt;
  }
  std::optional<LogicValue>
  application(const LogicFunctionDecl &,
              const std::vector<LogicValue> &) override {
    return std::nullopt;
  }
};

bool isDefinedness(ObligationKind Kind) {
  switch (Kind) {
  case ObligationKind::Overflow:
  case ObligationKind::DivisionByZero:
  case ObligationKind::Shift:
  case ObligationKind::Bounds:
  case ObligationKind::Dereference:
  case ObligationKind::Initialization:
  case ObligationKind::PointerDifference:
  case ObligationKind::PointerValidity:
    return true;
  default:
    return false;
  }
}

/// A place in the source: by its location in a run from source, by its
/// file, line, and column in an archive.
struct Anchor {
  SourceLocation Loc;
  ObligationSource Source;

  bool isValid() const { return Loc.isValid() || Source.isValid(); }
  bool at(const LogicExpr &E) const {
    if (Loc.isValid())
      return E.Loc == Loc;
    return E.Source.isValid() && E.Source.File == Source.File &&
           E.Source.Line == Source.Line && E.Source.Column == Source.Column;
  }
};
} // namespace

FailurePlace verify::failingPlace(const ObligationModule &Module,
                                  const VerifyResult &Failure) {
  FailurePlace Place;
  auto Item = llvm::find_if(Module.Obligations, [&](const Obligation &O) {
    return !Failure.ObligationId.empty() &&
           (O.StableId == Failure.ObligationId || O.Id == Failure.ObligationId);
  });
  if (Item == Module.Obligations.end() || !Item->Goal)
    return Place;
  const bool AtCall = Item->Clause.isValid() || Item->ClauseSource.isValid();
  Anchor Where;
  if (AtCall)
    Where = {Item->Clause.Loc, Item->ClauseSource};
  else if (Item->Focus.isValid() || Item->FocusSource.isValid())
    Where = {Item->Focus.Loc, Item->FocusSource};
  else
    Where = {Item->Loc, Item->Source};
  if (!Where.isValid())
    return Place;
  const LogicExpr *Checked = Item->Goal.get();
  while (Checked->K == LogicExpr::Or && !Checked->Premise.empty() &&
         Checked->Children.size() == 2)
    Checked = Checked->Children[1].get();
  const LogicExpr *Condition = nullptr;
  std::function<void(const LogicExpr *)> find = [&](const LogicExpr *E) {
    if (Condition || !E)
      return;
    if (Where.at(*E)) {
      // A path condition around the condition takes its place.
      if (E->K == LogicExpr::Or && E->Children.size() == 2 &&
          Where.at(*E->Children[1]))
        find(E->Children[1].get());
      if (!Condition)
        Condition = E;
      return;
    }
    for (const auto &Child : E->Children)
      find(Child.get());
  };
  find(Checked);
  std::optional<AssignedValues> Model;
  if (Failure.Assignment)
    Model.emplace(*Failure.Assignment);
  CertifyLimits Limits;
  Limits.Deadline = std::chrono::steady_clock::now() + std::chrono::seconds(1);
  auto isFalse = [&](const LogicExpr *E) {
    if (!Model)
      return false;
    std::optional<LogicValue> Value = evaluateTerm(Module, *E, *Model, Limits);
    return Value && Value->K == LogicValue::Kind::Bool && !Value->Truth;
  };
  auto placed = [](const LogicExpr *E) {
    return E->Loc.isValid() || E->Source.isValid();
  };
  const bool Generated = isDefinedness(Item->Kind);
  std::function<const LogicExpr *(const LogicExpr *)> falsePart =
      [&](const LogicExpr *E) -> const LogicExpr * {
    if (E->K == LogicExpr::And) {
      std::vector<const LogicExpr *> Conjuncts;
      std::function<void(const LogicExpr *)> flatten = [&](const LogicExpr *C) {
        if (C->K == LogicExpr::And)
          for (const auto &Child : C->Children)
            flatten(Child.get());
        else
          Conjuncts.push_back(C);
      };
      flatten(E);
      for (const LogicExpr *Conjunct : Conjuncts)
        if (isFalse(Conjunct))
          if (const LogicExpr *Part = falsePart(Conjunct))
            return Part;
      return nullptr;
    }
    if (Generated && E->K == LogicExpr::Or && E->Children.size() == 2 &&
        E->Children[0]->K == LogicExpr::Not && isFalse(E->Children[0].get()) &&
        isFalse(E->Children[1].get()))
      if (const LogicExpr *Part = falsePart(E->Children[1].get()))
        return Part;
    return placed(E) ? E : nullptr;
  };
  const LogicExpr *Part = Condition ? falsePart(Condition) : nullptr;
  auto spanOf = [](const LogicExpr &E) -> SourceSpan {
    if (!E.Loc.isValid())
      return {};
    return {E.Loc, E.BeginLoc.isValid() ? E.BeginLoc : E.Loc,
            E.EndLoc.isValid() ? E.EndLoc : E.Loc};
  };
  if (AtCall) {
    Place.At = Item->Focus;
    Place.AtSource = Item->FocusSource;
    Place.Clause = Part ? spanOf(*Part) : Item->Clause;
    Place.ClauseSource = Part ? Part->Source : Item->ClauseSource;
    return Place;
  }
  if (Part) {
    Place.At = spanOf(*Part);
    Place.AtSource = Part->Source;
  }
  return Place;
}

std::string verify::clauseNote(const VerifyResult &Failure) {
  return Failure.ObligationType == ObligationKind::Precondition
             ? "this precondition does not hold at the call"
             : "this clause does not hold at the call";
}
