set(LLVM_LINK_COMPONENTS
  Support
  )

if(NOT TARGET clangVerify)
  return()
endif()

add_clang_tool(cpp-verify
  Main.cpp
  )

target_link_libraries(cpp-verify
  PRIVATE
  clangVerify
  clangFrontend
  clangTooling
  clangDriver
  )

if(CPPVERIFY_ENABLE_COVERAGE)
  target_link_options(cpp-verify PRIVATE -fprofile-instr-generate)
endif()