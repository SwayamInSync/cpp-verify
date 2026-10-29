set(LLVM_LINK_COMPONENTS
  FuzzerCLI
  Support
  )

if(NOT TARGET clangVerify)
  return()
endif()

# With -DLLVM_USE_SANITIZE_COVERAGE=On (and a Clang host compiler) this is a
# libFuzzer binary; otherwise it runs its target on the files it is given.
add_llvm_fuzzer(cpp-verify-archive-fuzzer
  ArchiveFuzzer.cpp
  DUMMY_MAIN DummyArchiveFuzzer.cpp
  )

target_link_libraries(cpp-verify-archive-fuzzer
  PRIVATE
  clangVerify
  )
