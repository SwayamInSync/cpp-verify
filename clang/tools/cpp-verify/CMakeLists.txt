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

get_property(_cppverify_sanitize_flags GLOBAL PROPERTY CPPVERIFY_SANITIZE_FLAGS)
if(_cppverify_sanitize_flags)
  target_compile_options(cpp-verify PRIVATE ${_cppverify_sanitize_flags})
  target_link_options(cpp-verify PRIVATE ${_cppverify_sanitize_flags})
endif()