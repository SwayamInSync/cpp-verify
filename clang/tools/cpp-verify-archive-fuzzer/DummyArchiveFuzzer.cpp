//===--- DummyArchiveFuzzer.cpp - run the archive fuzzer on files ---------===//
//
// Without libFuzzer, the fuzzer runs its target on each file it is given, as
// the regression test does with the corpus.
//
//===----------------------------------------------------------------------===//
#include "llvm/FuzzMutate/FuzzerCLI.h"
#include <cstddef>
#include <cstdint>

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *Data, size_t Size);
extern "C" int LLVMFuzzerInitialize(int *argc, char ***argv);

int main(int argc, char *argv[]) {
  return llvm::runFuzzerOnInputs(argc, argv, LLVMFuzzerTestOneInput,
                                 LLVMFuzzerInitialize);
}
