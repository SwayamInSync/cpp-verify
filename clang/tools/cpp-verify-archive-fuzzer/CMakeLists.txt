set(LLVM_LINK_COMPONENTS
  FuzzerCLI
  Support
  )

if(NOT TARGET clangVerify)
  return()
endif()

# With -DLLVM_USE_SANITIZE_COVERAGE=On (and a Clang host compiler) this is a
# libFuzzer binary; otherwise it runs its target on the files it is given.
# It is then compiled with -fsanitize=fuzzer, which a precompiled header of
# the libraries it links is not, so it cannot reuse one.
add_llvm_fuzzer(cpp-verify-archive-fuzzer
  ArchiveFuzzer.cpp
  DISABLE_PCH_REUSE
  DUMMY_MAIN DummyArchiveFuzzer.cpp
  )

target_link_libraries(cpp-verify-archive-fuzzer
  PRIVATE
  clangVerify
  )
