//===- EncodingParityTest.cpp - Per-obligation encoding parity ------------===//
//
// Decisive verdicts must match across encodings for every archived obligation.
// Env: CPPVERIFY_PARITY_ARCHIVES, CPPVERIFY_PARITY_TIMEOUT_MS,
// CPPVERIFY_PARITY_CVC5.
//
//===----------------------------------------------------------------------===//

#include "Backend/CVC5Backend.h"
#include "Backend/ObligationSerialization.h"
#include "Backend/ObligationSimplify.h"
#include "Backend/Z3Encode.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/Path.h"
#include "gtest/gtest.h"
#include <cstdlib>
#include <map>

using namespace clang::verify;

namespace {

enum class Verdict { Proved, Refuted, Unknown };

Verdict verdictOf(const VerifyResult &Result) {
  if (Result.Status == VerifyStatus::Verified)
    return Verdict::Proved;
  if (Result.Status == VerifyStatus::Failed)
    return Verdict::Refuted;
  return Verdict::Unknown;
}

const char *nameOf(Verdict V) {
  switch (V) {
  case Verdict::Proved:
    return "proved";
  case Verdict::Refuted:
    return "refuted";
  case Verdict::Unknown:
    return "unknown";
  }
  return "?";
}

unsigned environmentNumber(const char *Name, unsigned Default) {
  const char *Value = std::getenv(Name);
  return Value && *Value ? static_cast<unsigned>(std::atoi(Value)) : Default;
}

TEST(EncodingParityTest, EveryObligationAgreesAcrossEncodings) {
  const char *Directory = std::getenv("CPPVERIFY_PARITY_ARCHIVES");
  if (!Directory || !*Directory)
    GTEST_SKIP()
        << "set CPPVERIFY_PARITY_ARCHIVES to run the corpus parity check";
  const unsigned TimeoutMs =
      environmentNumber("CPPVERIFY_PARITY_TIMEOUT_MS", 10000);
  const bool WithCVC5 = environmentNumber("CPPVERIFY_PARITY_CVC5", 0) != 0;

  std::vector<std::string> Archives;
  std::error_code EC;
  for (llvm::sys::fs::directory_iterator It(Directory, EC), End;
       It != End && !EC; It.increment(EC))
    if (llvm::sys::path::extension(It->path()) == ".cpv")
      Archives.push_back(It->path());
  ASSERT_FALSE(EC) << EC.message();
  ASSERT_FALSE(Archives.empty()) << "no .cpv archives in " << Directory;
  std::sort(Archives.begin(), Archives.end());

  // Keyed by "<integer>/<bitvector>" verdict pair, per solver.
  std::map<std::string, unsigned> Tally;
  unsigned Obligations = 0;
  for (const std::string &Path : Archives) {
    auto Buffer = llvm::MemoryBuffer::getFile(Path);
    ASSERT_TRUE(static_cast<bool>(Buffer)) << Path;
    auto Modules = deserializeObligationModules((*Buffer)->getBuffer());
    ASSERT_TRUE(static_cast<bool>(Modules))
        << Path << ": " << llvm::toString(Modules.takeError());
    for (ObligationModule &Decoded : *Modules) {
      auto Simplified = simplifyObligationModule(std::move(Decoded));
      ASSERT_TRUE(static_cast<bool>(Simplified))
          << Path << ": " << llvm::toString(Simplified.takeError());
      const ObligationModule &Module = *Simplified;
      auto solveZ3 = [&](const Obligation &Item, MachineIntegerEncoding E) {
        Z3Encoder Encoder;
        Encoder.setTimeoutMs(TimeoutMs);
        Encoder.setIntegerEncoding(E);
        return verdictOf(Encoder.verifyModule(
            Module, Item.CounterexampleQuery.get(), Item.TraceEventCount));
      };
      std::vector<Verdict> CVC5Integer, CVC5BitVector;
      if (WithCVC5) {
        for (MachineIntegerEncoding E : {MachineIntegerEncoding::Integer,
                                         MachineIntegerEncoding::BitVector}) {
          BackendExecutionOptions Execution;
          Execution.SolverTimeoutMs = TimeoutMs;
          Execution.IntegerEncoding = E;
          std::vector<Verdict> &Out = E == MachineIntegerEncoding::Integer
                                          ? CVC5Integer
                                          : CVC5BitVector;
          for (const VerifyResult &R :
               CVC5VerifyBackend(Execution).verifyObligations(Module))
            Out.push_back(verdictOf(R));
        }
      }
      for (size_t I = 0; I != Module.Obligations.size(); ++I) {
        const Obligation &Item = Module.Obligations[I];
        ++Obligations;
        const std::string Where =
            llvm::sys::path::filename(Path).str() + " " + Module.FunctionName +
            " " + (Item.StableId.empty() ? Item.Id : Item.StableId);
        auto compare = [&](const char *Solver, Verdict Integer, Verdict Bits) {
          ++Tally[std::string(Solver) + " " + nameOf(Integer) + "/" +
                  nameOf(Bits)];
          if (Integer != Verdict::Unknown && Bits != Verdict::Unknown)
            EXPECT_EQ(Integer, Bits)
                << Solver << " encodings disagree on " << Where << ": integer "
                << nameOf(Integer) << ", bitvector " << nameOf(Bits);
        };
        const Verdict Z3Integer =
            solveZ3(Item, MachineIntegerEncoding::Integer);
        const Verdict Z3BitVector =
            solveZ3(Item, MachineIntegerEncoding::BitVector);
        compare("z3", Z3Integer, Z3BitVector);
        if (Z3BitVector != Verdict::Unknown && Z3Integer == Verdict::Unknown)
          llvm::errs() << "note: only the bit-vector encoding decided " << Where
                       << "\n";
        if (WithCVC5 && I < CVC5Integer.size() && I < CVC5BitVector.size()) {
          compare("cvc5", CVC5Integer[I], CVC5BitVector[I]);
          // Every decisive verdict must agree across solvers as well.
          for (Verdict Other : {CVC5Integer[I], CVC5BitVector[I]})
            for (Verdict Mine : {Z3Integer, Z3BitVector})
              if (Other != Verdict::Unknown && Mine != Verdict::Unknown)
                EXPECT_EQ(Mine, Other) << "z3 and cvc5 disagree on " << Where;
        }
      }
    }
  }
  llvm::errs() << "parity: " << Obligations << " obligations in "
               << Archives.size() << " archives (integer/bitvector)\n";
  for (const auto &[Pair, Count] : Tally)
    llvm::errs() << "  " << Pair << ": " << Count << "\n";
}

} // namespace
