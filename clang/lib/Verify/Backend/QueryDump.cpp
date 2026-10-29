//===--- QueryDump.cpp - Solver queries as SMT-LIB scripts ----------------===//
#include "QueryDump.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/SHA256.h"
#include "llvm/Support/raw_ostream.h"
#include <mutex>

using namespace clang;
using namespace verify;

namespace {
struct DumpSettings {
  std::mutex Lock;
  std::string Directory;
  std::string Tool;
  std::string Error;
};

DumpSettings &settings() {
  static DumpSettings Settings;
  return Settings;
}

void recordError(std::string Message) {
  DumpSettings &S = settings();
  std::lock_guard<std::mutex> Guard(S.Lock);
  if (S.Error.empty())
    S.Error = std::move(Message);
}

std::string digest(llvm::StringRef Text, size_t Digits) {
  llvm::SHA256 Hash;
  Hash.update(Text);
  return llvm::toHex(Hash.final(), /*LowerCase=*/true).substr(0, Digits);
}

/// \p Name with every character but letters, digits, `_`, and \p Kept
/// replaced by `_`, so that it names a file on every system.
std::string fileName(llvm::StringRef Name, llvm::StringRef Kept = "") {
  std::string Out;
  for (char C : Name.take_front(64))
    Out += llvm::isAlnum(C) || C == '_' || Kept.contains(C) ? C : '_';
  return Out;
}

const Obligation *obligationOf(const ObligationModule *Module,
                               const LogicExpr *Query) {
  if (Module && Query)
    for (const Obligation &Item : Module->Obligations)
      if (Item.CounterexampleQuery.get() == Query)
        return &Item;
  return nullptr;
}

bool wholeQuery(const ObligationModule *Module, const LogicExpr *Query) {
  return Module && (!Query || Query == Module->CounterexampleQuery.get());
}

llvm::StringRef stableId(const Obligation &Item) {
  return Item.StableId.empty() ? Item.Id : Item.StableId;
}
} // namespace

void verify::setQueryDumpDirectory(std::string Directory, std::string Tool) {
  DumpSettings &S = settings();
  std::lock_guard<std::mutex> Guard(S.Lock);
  S.Directory = std::move(Directory);
  S.Tool = std::move(Tool);
  S.Error.clear();
}

bool verify::queryDumpEnabled() {
  DumpSettings &S = settings();
  std::lock_guard<std::mutex> Guard(S.Lock);
  return !S.Directory.empty();
}

std::string verify::queryDumpError() {
  DumpSettings &S = settings();
  std::lock_guard<std::mutex> Guard(S.Lock);
  return S.Error;
}

std::string verify::queryDumpPath(const ObligationModule *Module,
                                  const LogicExpr *Query,
                                  llvm::StringRef Solver,
                                  llvm::StringRef Script) {
  std::string Function = "query";
  if (Module) {
    Function = fileName(Module->FunctionName);
    Function += "-" + digest(Module->FunctionIdentity, 6);
  }
  // An obligation by its stable id, `postcondition@11:23` as
  // `postcondition-11-23`.
  std::string Name = "query";
  if (wholeQuery(Module, Query)) {
    Name = "whole";
  } else if (const Obligation *Item = obligationOf(Module, Query)) {
    llvm::StringRef Id = stableId(*Item);
    std::string Local =
        Id.contains("::") ? Id.rsplit("::").second.str() : Id.str();
    for (char &C : Local)
      if (C == '@' || C == ':' || C == '#')
        C = '-';
    Name = fileName(Local, "-");
  }
  llvm::SmallString<128> Path(Function);
  llvm::sys::path::append(Path, Name + "." + Solver.str() + "-" +
                                    digest(Script, 8) + ".smt2");
  return std::string(Path);
}

void QueryDump::start(const ObligationModule *Module, const LogicExpr *Query,
                      llvm::StringRef Solver, llvm::StringRef SolverVersion,
                      llvm::StringRef Options, llvm::StringRef Script) {
  std::string Directory, Tool;
  {
    DumpSettings &S = settings();
    std::lock_guard<std::mutex> Guard(S.Lock);
    Directory = S.Directory;
    Tool = S.Tool;
  }
  if (Directory.empty())
    return;
  const std::string Relative = queryDumpPath(Module, Query, Solver, Script);
  llvm::SmallString<256> Full(Directory);
  llvm::sys::path::append(Full, Relative);
  if (std::error_code EC = llvm::sys::fs::create_directories(
          llvm::sys::path::parent_path(Full))) {
    recordError("cannot create " + llvm::sys::path::parent_path(Full).str() +
                ": " + EC.message());
    return;
  }

  std::string Text;
  llvm::raw_string_ostream OS(Text);
  OS << "; " << Tool << ", " << Solver << ' ' << SolverVersion << "\n";
  if (Module) {
    OS << "; " << Module->FunctionName << ": ";
    if (wholeQuery(Module, Query)) {
      OS << "every obligation at once";
    } else if (const Obligation *Item = obligationOf(Module, Query)) {
      OS << "the " << obligationKindName(Item->Kind) << " check";
      if (Item->Source.isValid())
        OS << " at " << Item->Source.File << ':' << Item->Source.Line << ':'
           << Item->Source.Column;
      OS << " (" << stableId(*Item) << ")";
    } else {
      OS << "a query built from its obligations";
    }
    OS << "\n";
  }
  OS << "; replay: " << Solver << ' ' << Relative << "\n";
  OS << Options << Script;

  // Written whole under a temporary name, so that a reader never sees a
  // part of it.
  int FD = -1;
  llvm::SmallString<256> Temporary;
  if (std::error_code EC = llvm::sys::fs::createUniqueFile(Full + ".%%%%%%.tmp",
                                                           FD, Temporary)) {
    recordError("cannot write " + Full.str().str() + ": " + EC.message());
    return;
  }
  {
    llvm::raw_fd_ostream Out(FD, /*shouldClose=*/true);
    Out << Text;
    Out.close();
    if (Out.has_error()) {
      recordError("cannot write " + Full.str().str() + ": " +
                  Out.error().message());
      Out.clear_error();
      llvm::sys::fs::remove(Temporary);
      return;
    }
  }
  if (std::error_code EC = llvm::sys::fs::rename(Temporary, Full)) {
    recordError("cannot write " + Full.str().str() + ": " + EC.message());
    llvm::sys::fs::remove(Temporary);
    return;
  }
  Path = std::string(Full);
}

void QueryDump::finish(llvm::StringRef Answer, llvm::StringRef Commands) {
  if (Path.empty())
    return;
  std::error_code EC;
  llvm::raw_fd_ostream Out(Path, EC, llvm::sys::fs::OF_Append);
  if (!EC) {
    Out << Commands << "; cpp-verify: " << Answer << "\n";
    Out.close();
    if (Out.has_error()) {
      EC = Out.error();
      Out.clear_error();
    }
  }
  if (EC)
    recordError("cannot write " + Path + ": " + EC.message());
  Path.clear();
}
