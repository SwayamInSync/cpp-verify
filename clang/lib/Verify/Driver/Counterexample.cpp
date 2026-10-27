//===--- Counterexample.cpp -----------------------------------------------===//
#include "Counterexample.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringRef.h"
#include <algorithm>
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
