//===--- CppVerifyVersion.cpp - cpp-verify and backend versions -----------===//
#include "CppVerifyVersion.h"
#include "clang/Basic/Version.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Config/llvm-config.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/FileUtilities.h"
#include "llvm/Support/FormatVariadic.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/Program.h"
#include "llvm/TargetParser/Host.h"
#include <optional>
#include <string>
#include <z3.h>

using namespace clang;
using namespace verify;

namespace {

/// The standard output of Program run with Arguments, when it exits with 0.
std::optional<std::string>
runForOutput(llvm::StringRef Program,
             llvm::ArrayRef<llvm::StringRef> Arguments) {
  llvm::SmallString<128> OutputPath;
  if (llvm::sys::fs::createTemporaryFile("cppverify-version", "txt",
                                         OutputPath))
    return std::nullopt;
  llvm::FileRemover Remove(OutputPath);
  std::optional<llvm::StringRef> Redirects[] = {
      llvm::StringRef(), llvm::StringRef(OutputPath), llvm::StringRef()};
  if (llvm::sys::ExecuteAndWait(Program, Arguments, std::nullopt, Redirects,
                                /*SecondsToWait=*/10) != 0)
    return std::nullopt;
  auto Buffer = llvm::MemoryBuffer::getFile(OutputPath);
  if (!Buffer)
    return std::nullopt;
  return Buffer.get()->getBuffer().str();
}

/// The dotted number after Marker in Text: "1.1.2" in "cvc5 version 1.1.2".
llvm::StringRef numberAfter(llvm::StringRef Text, llvm::StringRef Marker) {
  size_t At = Text.find(Marker);
  if (At == llvm::StringRef::npos)
    return {};
  return Text.substr(At + Marker.size()).ltrim().take_while([](char C) {
    return llvm::isDigit(C) || C == '.';
  });
}

void printRow(llvm::raw_ostream &OS, llvm::StringRef Backend,
              llvm::StringRef Version, const llvm::Twine &Detail) {
  OS << llvm::formatv("  {0,-6} {1,-8} ", Backend, Version) << Detail << "\n";
}

void printCVC5(llvm::raw_ostream &OS) {
  std::string Tested = ("tested with " + CVC5TestedVersion).str();
  auto Program = llvm::sys::findProgramByName("cvc5");
  if (!Program) {
    printRow(OS, "cvc5", "missing",
             "not on PATH; --backend=cvc5, portfolio, and race run it (" +
                 Tested + ")");
    return;
  }
  std::optional<std::string> Output =
      runForOutput(*Program, {*Program, "--version"});
  llvm::StringRef Version =
      Output ? numberAfter(*Output, "cvc5 version") : llvm::StringRef();
  printRow(OS, "cvc5", Version.empty() ? "unknown" : Version,
           *Program + " (" + Tested + ")");
}

void printLean(llvm::raw_ostream &OS) {
  llvm::StringRef Pinned = LeanToolchain.substr(LeanToolchain.find(":v") + 2);
  auto Lake = llvm::sys::findProgramByName("lake");
  if (!Lake) {
    printRow(OS, "lean", "missing",
             "lake is not on PATH; --lean-certify runs it (projects pin " +
                 LeanToolchain + ")");
    return;
  }
  // Under elan, lake runs the toolchain each project pins and may download
  // it, so ask elan whether the pin is installed instead of running lake.
  auto Elan = llvm::sys::findProgramByName("elan");
  bool ViaElan = false;
  if (!Elan || llvm::sys::fs::equivalent(*Lake, *Elan, ViaElan))
    ViaElan = false;
  if (ViaElan) {
    std::optional<std::string> Installed =
        runForOutput(*Elan, {*Elan, "toolchain", "list"});
    bool HasPin = false;
    if (Installed) {
      llvm::SmallVector<llvm::StringRef> Lines;
      llvm::StringRef(*Installed).split(Lines, '\n');
      for (llvm::StringRef Line : Lines)
        HasPin |= Line.trim().split(' ').first == LeanToolchain;
    }
    printRow(
        OS, "lean", Pinned,
        *Lake + " (elan; projects pin " + LeanToolchain +
            (HasPin ? ", installed)" : ", which elan installs on first use)"));
    return;
  }
  std::optional<std::string> Output = runForOutput(*Lake, {*Lake, "--version"});
  llvm::StringRef Version =
      Output ? numberAfter(*Output, "Lean version") : llvm::StringRef();
  if (Version == Pinned) {
    printRow(OS, "lean", Version,
             *Lake + " (projects pin " + LeanToolchain + ")");
    return;
  }
  printRow(OS, "lean", Version.empty() ? "unknown" : Version,
           *Lake + ", but projects pin " + LeanToolchain);
}

} // namespace

void verify::printVersion(llvm::raw_ostream &OS) {
  OS << "cpp-verify " << CPPVERIFY_VERSION;
  std::string Repository = getClangFullRepositoryVersion();
  if (!Repository.empty())
    OS << ' ' << Repository;
  OS << "\n  based on LLVM " << LLVM_VERSION_STRING;
#ifndef NDEBUG
  OS << ", with assertions";
#endif
  OS << "\n  default target: " << llvm::sys::getDefaultTargetTriple()
     << "\n\nVerification backends:\n";

  unsigned Major = 0, Minor = 0, Build = 0, Revision = 0;
  Z3_get_version(&Major, &Minor, &Build, &Revision);
  printRow(OS, "z3", llvm::formatv("{0}.{1}.{2}", Major, Minor, Build).str(),
           "built in (" CPPVERIFY_Z3_ORIGIN ")");
  printCVC5(OS);
  printLean(OS);
  OS << "  bmc uses z3; portfolio and race use z3 and cvc5\n";
}
