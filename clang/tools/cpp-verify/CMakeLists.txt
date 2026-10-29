set(LLVM_LINK_COMPONENTS
  Support
  )

if(NOT TARGET clangVerify)
  return()
endif()

get_property(_cppverify_sanitize_flags GLOBAL PROPERTY CPPVERIFY_SANITIZE_FLAGS)
set(_cppverify_pch_reuse)
if(_cppverify_sanitize_flags)
  set(_cppverify_pch_reuse DISABLE_PCH_REUSE)
endif()

# Under ThreadSanitizer, a nesting deeper than its shadow stack holds stops
# the run with its stack instead of corrupting the runtime.
set(LLVM_OPTIONAL_SOURCES ShadowStackGuard.cpp)
set(_cppverify_shadow_stack_guard)
if((_cppverify_sanitize_flags MATCHES "thread" OR
    LLVM_USE_SANITIZER MATCHES "Thread") AND NOT APPLE)
  set(_cppverify_shadow_stack_guard ShadowStackGuard.cpp)
  set_source_files_properties(ShadowStackGuard.cpp PROPERTIES
    COMPILE_OPTIONS -fno-sanitize=thread SKIP_PRECOMPILE_HEADERS ON)
endif()

add_clang_tool(cpp-verify
  Main.cpp
  ${_cppverify_shadow_stack_guard}
  ${_cppverify_pch_reuse}
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

if(_cppverify_sanitize_flags)
  target_compile_options(cpp-verify PRIVATE ${_cppverify_sanitize_flags})
  target_link_options(cpp-verify PRIVATE ${_cppverify_sanitize_flags})
endif()

if(_cppverify_shadow_stack_guard)
  target_link_options(cpp-verify PRIVATE
    -Wl,--wrap=__tsan_func_entry,--wrap=__tsan_func_exit)
endif()