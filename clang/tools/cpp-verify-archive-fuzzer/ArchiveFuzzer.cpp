//===--- ArchiveFuzzer.cpp - fuzz the obligation archive reader -----------===//
//
// An archive given to --obligation-in is untrusted input. Every byte string
// is either rejected with an error or decodes to modules that validate, that
// the writer states again byte for byte with the same semantic hashes, whose
// canonical form validates and is a fixpoint, and that every adapter lowers
// without a solver. A property that does not hold aborts, which libFuzzer
// reports as a crash with the input that shows it.
//
//===----------------------------------------------------------------------===//
#include "Backend/CVC5Backend.h"
#include "Backend/LeanBackend.h"
#include "Backend/ObligationSerialization.h"
#include "Backend/ObligationSimplify.h"
#include "Backend/VerifyBackend.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/Twine.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdint>
#include <cstdlib>
#include <set>
#include <string>

namespace verify = clang::verify;

namespace {

[[noreturn]] void fail(const llvm::Twine &Property,
                       const llvm::Twine &Detail = "") {
  llvm::errs() << "archive fuzzer: " << Property;
  if (!Detail.isTriviallyEmpty())
    llvm::errs() << ": " << Detail;
  llvm::errs() << "\n";
  std::abort();
}

/// The record of Module reads back as Module.
void checkRoundTrip(const verify::ObligationModule &Module,
                    llvm::StringRef Stage) {
  const std::string Record = verify::serializeObligationModule(Module);
  auto Read = verify::deserializeObligationModules(Record);
  if (!Read)
    fail("the record of a " + Stage + " module does not read back",
         llvm::toString(Read.takeError()));
  if (Read->size() != 1)
    fail("the record of a " + Stage + " module reads back as " +
         llvm::Twine(Read->size()) + " modules");
  const verify::ObligationModule &Again = Read->front();
  if (verify::serializeObligationModule(Again) != Record)
    fail("the record of a " + Stage + " module is not stated again exactly");
  if (verify::obligationSemanticHash(Again) !=
      verify::obligationSemanticHash(Module))
    fail("a " + Stage + " module read back has another semantic hash");
  if (Again.Obligations.size() != Module.Obligations.size())
    fail("a " + Stage + " module read back has other obligations");
  for (size_t I = 0; I != Module.Obligations.size(); ++I) {
    const verify::Obligation &Item = Module.Obligations[I];
    const verify::Obligation &ItemAgain = Again.Obligations[I];
    if (verify::obligationSemanticHash(Again, ItemAgain) !=
            verify::obligationSemanticHash(Module, Item) ||
        verify::obligationStatementHash(Again, ItemAgain) !=
            verify::obligationStatementHash(Module, Item) ||
        verify::obligationQuerySemanticHash(Again, ItemAgain) !=
            verify::obligationQuerySemanticHash(Module, Item))
      fail("an obligation of a " + Stage +
           " module read back has another hash");
  }
}

/// Every adapter replay can reach lowers Module without a solver. A result
/// other than Lowered is a verdict replay reports, never a property broken.
void lowerEverywhere(const verify::ObligationModule &Module) {
  for (verify::MachineIntegerEncoding Encoding :
       {verify::MachineIntegerEncoding::Auto,
        verify::MachineIntegerEncoding::Integer,
        verify::MachineIntegerEncoding::BitVector}) {
    verify::BackendExecutionOptions Execution;
    Execution.IntegerEncoding = Encoding;
    (void)verify::lowerObligationModule(Module, nullptr, Execution);
    (void)verify::lowerSMTLibModule(Module, nullptr, Execution);
  }
  // Lean replay rejects a bounded module before it exports anything.
  if (Module.BMCTransform)
    return;
  std::string Text;
  llvm::raw_string_ostream OS(Text);
  std::set<std::string> Functions;
  std::set<std::string> Theorems;
  (void)verify::exportLeanScratchPad(Module, OS, /*EmitPreamble=*/true,
                                     Functions, Theorems, /*ModuleIndex=*/0,
                                     /*ProjectGoals=*/nullptr);
}

} // namespace

extern "C" int LLVMFuzzerInitialize(int *, char ***) { return 0; }

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *Data, size_t Size) {
  auto Modules = verify::deserializeObligationModules(
      llvm::StringRef(reinterpret_cast<const char *>(Data), Size));
  if (!Modules) {
    llvm::consumeError(Modules.takeError());
    return 0;
  }
  for (verify::ObligationModule &Module : *Modules) {
    if (auto Features = verify::validateObligationModule(Module); !Features)
      fail("a decoded module does not validate",
           llvm::toString(Features.takeError()));
    checkRoundTrip(Module, "decoded");
    auto Canonical = verify::simplifyObligationModule(std::move(Module));
    if (!Canonical)
      fail("a decoded module does not canonicalize",
           llvm::toString(Canonical.takeError()));
    checkRoundTrip(*Canonical, "canonical");
    auto Copy = verify::deserializeObligationModules(
        verify::serializeObligationModule(*Canonical));
    if (!Copy)
      fail("a canonical module does not read back",
           llvm::toString(Copy.takeError()));
    auto Again = verify::simplifyObligationModule(std::move(Copy->front()));
    if (!Again)
      fail("a canonical module does not canonicalize again",
           llvm::toString(Again.takeError()));
    if (verify::serializeObligationModule(*Again) !=
        verify::serializeObligationModule(*Canonical))
      fail("canonicalization is not a fixpoint");
    lowerEverywhere(*Canonical);
  }
  return 0;
}
