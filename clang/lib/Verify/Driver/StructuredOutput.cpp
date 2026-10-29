//===--- StructuredOutput.cpp - JSON, SARIF, and GitHub output ------------===//
#include "StructuredOutput.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Path.h"
#include <map>

using namespace clang;
using namespace clang::verify;

std::string verify::jsonText(llvm::StringRef Text) {
  return llvm::json::isUTF8(Text) ? Text.str() : llvm::json::fixUTF8(Text);
}

llvm::json::Object verify::sourceJSON(const ObligationSource &Source) {
  llvm::json::Object Result;
  if (!Source.isValid())
    return Result;
  Result["file"] = jsonText(Source.File);
  Result["line"] = Source.beginLine();
  Result["column"] = Source.beginColumn();
  Result["end_line"] = Source.EndLine != 0 ? Source.EndLine : Source.Line;
  Result["end_column"] =
      Source.EndColumn != 0 ? Source.EndColumn : Source.Column;
  return Result;
}

/// A path as GitHub resolves it: relative to the working directory, the
/// checkout in a workflow, when it lies under it.
std::string verify::workspacePath(llvm::StringRef File) {
  llvm::SmallString<256> Directory;
  if (llvm::sys::path::is_absolute(File) &&
      !llvm::sys::fs::current_path(Directory)) {
    Directory += llvm::sys::path::get_separator();
    if (File.starts_with(Directory))
      return File.drop_front(Directory.size()).str();
  }
  return File.str();
}

namespace {
/// The workflow command escapes of GitHub Actions: data escapes '%' and line
/// ends, a property also ':' and ','.
std::string escapeCommand(llvm::StringRef Text, bool Property) {
  std::string Out;
  for (char C : Text) {
    switch (C) {
    case '%':
      Out += "%25";
      break;
    case '\r':
      Out += "%0D";
      break;
    case '\n':
      Out += "%0A";
      break;
    case ':':
      Out += Property ? "%3A" : ":";
      break;
    case ',':
      Out += Property ? "%2C" : ",";
      break;
    default:
      Out += C;
    }
  }
  return Out;
}


/// An absolute file URI, as Clang writes it in SARIF.
std::string fileURI(llvm::StringRef File) {
  llvm::SmallString<256> Path(File);
  llvm::sys::fs::make_absolute(Path);
  llvm::sys::path::native(Path, llvm::sys::path::Style::posix);
  std::string URI = "file://";
  if (!llvm::StringRef(Path).starts_with("/"))
    URI += "/";
  for (char C : Path) {
    if (llvm::isAlnum(C) || llvm::StringRef("-._~/:").contains(C))
      URI += C;
    else
      URI += "%" + llvm::utohexstr(static_cast<unsigned char>(C), false, 2);
  }
  return URI;
}

std::string text(const llvm::json::Object &Record, llvm::StringRef Key) {
  if (std::optional<llvm::StringRef> Value = Record.getString(Key))
    return Value->str();
  return "";
}

struct Classification {
  std::string Rule;
  std::string Kind;
  std::string Level;
};

/// The SARIF rule, kind, and level of a record, after Frama-C's mapping of
/// property statuses: a proof passes, a failure fails, what no verdict
/// settles stays open.
Classification classify(const llvm::json::Object &Record) {
  const std::string Status = text(Record, "status");
  const std::string Severity = text(Record, "severity");
  if (Status == "failed") {
    std::string Rule = "failed";
    if (const llvm::json::Object *Obligation = Record.getObject("obligation"))
      if (std::optional<llvm::StringRef> Kind = Obligation->getString("kind"))
        Rule = Kind->str();
    return {Rule, "fail", "error"};
  }
  if (Status == "verified" || Status == "certified" ||
      Status == "mixed-proof" || Status == "proved-obligations")
    return {"verified", "pass", "none"};
  if (Status == "unresolved" || Status == "interrupted")
    return {Status, "open", "error"};
  if (Status == "bounded-safe")
    return {Status, "open", "warning"};
  if (Status == "trusted")
    return {Status, "review", "none"};
  if (Status == "exported")
    return {Status, "open", "note"};
  if (Status == "lowered")
    return {Status, "informational", "none"};
  if (Status == "frontend")
    return {"frontend",
            Severity == "error" || Severity == "warning" ? "fail"
                                                         : "informational",
            Severity == "error" || Severity == "warning" ? Severity : "note"};
  if (Severity == "warning")
    return {"warning", "fail", "warning"};
  return {Status.empty() ? "error" : Status, "fail",
          Severity == "error" ? "error" : "note"};
}

std::string ruleDescription(llvm::StringRef Rule) {
  if (Rule == "verified")
    return "The function's contract is proved.";
  if (Rule == "unresolved")
    return "No verdict settles the function; the reason says why.";
  if (Rule == "interrupted")
    return "The run was interrupted before the function's verification ended.";
  if (Rule == "bounded-safe")
    return "No check fails within the unrolling bound.";
  if (Rule == "trusted")
    return "The contract is assumed, not verified.";
  if (Rule == "exported")
    return "The obligations are exported to Lean, not yet certified.";
  if (Rule == "lowered")
    return "The obligations are lowered; no solver ran.";
  if (Rule == "frontend")
    return "A diagnostic of the compiler.";
  if (Rule == "warning")
    return "A warning of the verifier.";
  if (Rule == "failed" || Rule == "error")
    return "Verification failed.";
  return ("A " + Rule + " check fails.").str();
}

/// What the text output prints before a verdict's message, which a record
/// leaves to its status.
std::string verdictPrefix(llvm::StringRef Status) {
  static const std::pair<const char *, const char *> Prefixes[] = {
      {"verified", "Verified: "},
      {"certified", "Certified: "},
      {"mixed-proof", "Proved: "},
      {"proved-obligations", "Proved obligations: "},
      {"unresolved", "Unresolved: "},
      {"interrupted", "Interrupted: "},
      {"bounded-safe", "BoundedSafe: "},
      {"trusted", "Trusted: "},
      {"exported", "Exported: "},
      {"lowered", "Lowered: "}};
  for (const auto &[Name, Prefix] : Prefixes)
    if (Status == Name)
      return Prefix;
  return "";
}

llvm::json::Object region(const llvm::json::Object &Source) {
  static const std::pair<const char *, const char *> Fields[] = {
      {"line", "startLine"},
      {"column", "startColumn"},
      {"end_line", "endLine"},
      {"end_column", "endColumn"}};
  llvm::json::Object Region;
  for (const auto &[From, To] : Fields)
    if (std::optional<int64_t> Value = Source.getInteger(From))
      Region[To] = *Value;
  return Region;
}
} // namespace

std::string verify::githubCommand(llvm::StringRef Level,
                                  const ObligationSource &Source,
                                  llvm::StringRef Title,
                                  llvm::StringRef Message) {
  std::vector<std::string> Properties;
  if (Source.isValid()) {
    Properties.push_back("file=" +
                         escapeCommand(workspacePath(Source.File), true));
    Properties.push_back("line=" + std::to_string(Source.beginLine()));
    Properties.push_back("col=" + std::to_string(Source.beginColumn()));
    if (Source.EndLine) {
      Properties.push_back("endLine=" + std::to_string(Source.EndLine));
      Properties.push_back("endColumn=" + std::to_string(Source.EndColumn));
    }
  }
  if (!Title.empty())
    Properties.push_back("title=" + escapeCommand(Title, true));
  std::string Command = "::" + Level.str();
  if (!Properties.empty())
    Command += " " + llvm::join(Properties, ",");
  return Command + "::" + escapeCommand(Message, false) + "\n";
}

llvm::json::Value verify::sarifLog(llvm::ArrayRef<llvm::json::Value> Records,
                                   const SarifInvocation &Invocation) {
  std::vector<std::pair<std::string, std::string>> RuleLevels;
  std::map<std::string, size_t> RuleIndex;
  std::vector<std::string> Files;
  std::map<std::string, size_t> FileIndex;
  auto physical = [&](const llvm::json::Object &Source) {
    llvm::json::Object Location;
    const std::string File = text(Source, "file");
    if (File.empty())
      return Location;
    const std::string URI = fileURI(File);
    auto [It, Inserted] = FileIndex.try_emplace(URI, Files.size());
    if (Inserted)
      Files.push_back(URI);
    Location["artifactLocation"] = llvm::json::Object{
        {"uri", URI}, {"index", static_cast<int64_t>(It->second)}};
    Location["region"] = region(Source);
    return Location;
  };

  llvm::json::Array Results;
  llvm::json::Object Properties;
  llvm::json::Array Times;
  for (const llvm::json::Value &Value : Records) {
    const llvm::json::Object *Record = Value.getAsObject();
    if (!Record)
      continue;
    const std::string Schema = text(*Record, "schema");
    if (Schema == SummarySchema) {
      Properties["summary"] = llvm::json::Value(llvm::json::Object(*Record));
      continue;
    }
    if (Schema != DiagnosticSchema) {
      Times.push_back(llvm::json::Object(*Record));
      continue;
    }
    Classification Class = classify(*Record);
    auto [It, Inserted] = RuleIndex.try_emplace(Class.Rule, RuleLevels.size());
    if (Inserted)
      RuleLevels.emplace_back(Class.Rule,
                              Class.Level == "none" ? "note" : Class.Level);

    llvm::json::Object Result;
    Result["ruleId"] = Class.Rule;
    Result["ruleIndex"] = static_cast<int64_t>(It->second);
    Result["kind"] = Class.Kind;
    Result["level"] = Class.Level;
    std::string Message =
        verdictPrefix(text(*Record, "status")) + text(*Record, "message");
    if (std::string Values = text(*Record, "counterexample"); !Values.empty())
      Message += "\ncounterexample: " + Values;
    if (const llvm::json::Array *Notes = Record->getArray("notes"))
      for (const llvm::json::Value &Note : *Notes)
        if (std::optional<llvm::StringRef> Line = Note.getAsString())
          Message += "\n" + Line->str();
    Result["message"] = llvm::json::Object{{"text", Message}};

    const llvm::json::Object *Source = Record->getObject("source");
    if (!Source)
      Source = Record->getObject("function_source");
    llvm::json::Object Location;
    if (Source)
      if (llvm::json::Object Physical = physical(*Source); !Physical.empty())
        Location["physicalLocation"] = std::move(Physical);
    if (std::string Function = text(*Record, "function"); !Function.empty())
      Location["logicalLocations"] = llvm::json::Array{
          llvm::json::Object{{"name", Function}, {"kind", "function"}}};
    if (!Location.empty())
      Result["locations"] = llvm::json::Array{std::move(Location)};

    if (const llvm::json::Array *Trace = Record->getArray("trace")) {
      llvm::json::Array Steps;
      for (const llvm::json::Value &Step : *Trace) {
        const llvm::json::Object *Event = Step.getAsObject();
        if (!Event)
          continue;
        llvm::json::Object At;
        if (const llvm::json::Object *StepSource = Event->getObject("source"))
          if (llvm::json::Object Physical = physical(*StepSource);
              !Physical.empty())
            At["physicalLocation"] = std::move(Physical);
        At["message"] = llvm::json::Object{{"text", text(*Event, "text")}};
        Steps.push_back(llvm::json::Object{{"location", std::move(At)}});
      }
      if (!Steps.empty())
        Result["codeFlows"] = llvm::json::Array{llvm::json::Object{
            {"threadFlows", llvm::json::Array{llvm::json::Object{
                                {"locations", std::move(Steps)}}}}}};
    }

    if (const llvm::json::Array *Related = Record->getArray("related")) {
      llvm::json::Array Locations;
      for (const llvm::json::Value &Each : *Related) {
        const llvm::json::Object *Note = Each.getAsObject();
        if (!Note)
          continue;
        llvm::json::Object At;
        At["id"] = static_cast<int64_t>(Locations.size());
        if (const llvm::json::Object *NoteSource = Note->getObject("source"))
          if (llvm::json::Object Physical = physical(*NoteSource);
              !Physical.empty())
            At["physicalLocation"] = std::move(Physical);
        At["message"] = llvm::json::Object{{"text", text(*Note, "message")}};
        Locations.push_back(std::move(At));
      }
      if (!Locations.empty())
        Result["relatedLocations"] = std::move(Locations);
    }

    llvm::json::Object Bag;
    for (const char *Key :
         {"status", "reason", "backend", "counterexample", "option"})
      if (std::string Value = text(*Record, Key); !Value.empty())
        Bag[Key] = Value;
    if (const llvm::json::Object *Obligation = Record->getObject("obligation"))
      if (std::optional<llvm::StringRef> Id = Obligation->getString("id"))
        Bag["obligation"] = Id->str();
    if (!Bag.empty())
      Result["properties"] = std::move(Bag);
    Results.push_back(std::move(Result));
  }
  if (!Times.empty())
    Properties["times"] = std::move(Times);

  llvm::json::Array Rules;
  for (const auto &[Id, Level] : RuleLevels)
    Rules.push_back(llvm::json::Object{
        {"id", Id},
        {"shortDescription", llvm::json::Object{{"text", ruleDescription(Id)}}},
        {"helpUri", "https://swayaminsync.github.io/cpp-verify/language/"
                    "tooling.html#structured-diagnostics"},
        {"defaultConfiguration", llvm::json::Object{{"level", Level}}}});
  llvm::json::Array Artifacts;
  for (const std::string &URI : Files)
    Artifacts.push_back(
        llvm::json::Object{{"location", llvm::json::Object{{"uri", URI}}}});
  llvm::json::Array Arguments;
  for (const std::string &Argument : Invocation.Arguments)
    Arguments.push_back(jsonText(Argument));

  llvm::json::Object Run;
  Run["tool"] = llvm::json::Object{
      {"driver",
       llvm::json::Object{
           {"name", "cpp-verify"},
           {"version", Invocation.Version},
           {"informationUri", "https://swayaminsync.github.io/cpp-verify/"},
           {"rules", std::move(Rules)}}}};
  Run["invocations"] = llvm::json::Array{
      llvm::json::Object{{"arguments", std::move(Arguments)},
                         {"executionSuccessful", Invocation.ExitCode != 130},
                         {"exitCode", Invocation.ExitCode}}};
  Run["artifacts"] = std::move(Artifacts);
  Run["columnKind"] = "unicodeCodePoints";
  Run["results"] = std::move(Results);
  if (!Properties.empty())
    Run["properties"] = std::move(Properties);
  return llvm::json::Object{
      {"$schema", "https://docs.oasis-open.org/sarif/sarif/v2.1.0/errata01/os/"
                  "schemas/sarif-schema-2.1.0.json"},
      {"version", "2.1.0"},
      {"runs", llvm::json::Array{std::move(Run)}}};
}
