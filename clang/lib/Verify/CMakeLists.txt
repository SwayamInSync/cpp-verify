set(LLVM_LINK_COMPONENTS
  Support
  )

include(${CMAKE_CURRENT_SOURCE_DIR}/../../cmake/modules/CppVerifyZ3.cmake)
cppverify_ensure_z3()

if(NOT CPPVERIFY_Z3_TARGET)
  message(STATUS
    "cpp-verify: Z3 unavailable (enable -DCPPVERIFY_VENDOR_Z3=ON or install system Z3)")
  return()
endif()
message(STATUS "cpp-verify: Z3 backend = ${CPPVERIFY_Z3_TARGET}")

option(CPPVERIFY_ENABLE_COVERAGE "Instrument clangVerify for LLVM coverage" OFF)
if(CPPVERIFY_ENABLE_COVERAGE)
  message(STATUS "cpp-verify: coverage instrumentation enabled")
endif()

# The verifier's own code under sanitizers, beside an uninstrumented LLVM,
# Clang, and Z3, as the nightly sanitizer job builds it: "address;undefined"
# or "thread". The precompiled header of the libraries it uses is built
# without them, so it is not reused.
set(CPPVERIFY_SANITIZER "" CACHE STRING
  "Sanitizers for clangVerify and cpp-verify (address;undefined, or thread)")
set(_cppverify_pch_reuse)
if(CPPVERIFY_SANITIZER)
  string(REPLACE ";" "," _cppverify_sanitizers "${CPPVERIFY_SANITIZER}")
  set(_cppverify_sanitize_flags
    -fsanitize=${_cppverify_sanitizers} -fno-omit-frame-pointer)
  # The verifier is built without RTTI.
  if(_cppverify_sanitizers MATCHES "undefined")
    list(APPEND _cppverify_sanitize_flags -fno-sanitize=vptr,function)
  endif()
  message(STATUS "cpp-verify: sanitizers ${_cppverify_sanitizers}")
  set(_cppverify_pch_reuse DISABLE_PCH_REUSE)
  set_property(GLOBAL PROPERTY CPPVERIFY_SANITIZE_FLAGS
    "${_cppverify_sanitize_flags}")
endif()

# A vendored Z3 installs its headers when its ExternalProject builds, so the
# sources that include them must wait for it (DEPENDS orders obj.clangVerify).
get_property(_cppverify_z3_ep GLOBAL PROPERTY CPPVERIFY_Z3_EP_TARGET)

add_clang_library(clangVerify
  IR/VExpr.cpp
  IR/VStmt.cpp
  IR/NodeBudget.cpp
  Frontend/ASTConverter.cpp
  Transform/Passivize.cpp
  Transform/Inductive.cpp
  Transform/InlineHelpers.cpp
  Transform/Origins.cpp
  Transform/Ownership.cpp
  Transform/OutParameters.cpp
  Transform/LoopUnroll.cpp
  Transform/SpecInline.cpp
  Transform/SubobjectBounds.cpp
  Transform/UBChecks.cpp
  Backend/Certify.cpp
  Backend/Presburger.cpp
  Backend/Obligation.cpp
  Backend/Induction.cpp
  Backend/ObligationSimplify.cpp
  Backend/ObligationSerialization.cpp
  Backend/ProofCache.cpp
  Backend/QueryDump.cpp
  Backend/ChildProcess.cpp
  Backend/CVC5Backend.cpp
  Backend/Z3Encode.cpp
  Backend/SpecAxioms.cpp
  Backend/VerifyBackend.cpp
  Backend/LeanBackend.cpp
  Driver/Verifier.cpp
  Driver/Counterexample.cpp
  Driver/StructuredOutput.cpp
  Driver/DumpIR.cpp
  Driver/CppVerifyIntegration.cpp
  Driver/CppVerifyVersion.cpp
  ${_cppverify_pch_reuse}

  LINK_LIBS
  clangAST
  clangBasic
  clangFrontend
  clangLex
  clangSema

  DEPENDS
  intrinsics_gen
  ${_cppverify_z3_ep}
)

target_link_libraries(clangVerify PRIVATE ${CPPVERIFY_Z3_TARGET})

get_property(_cppverify_z3_origin GLOBAL PROPERTY CPPVERIFY_Z3_ORIGIN)
set_property(SOURCE Driver/CppVerifyVersion.cpp APPEND PROPERTY COMPILE_DEFINITIONS
  CPPVERIFY_Z3_ORIGIN="${_cppverify_z3_origin}")

if(CPPVERIFY_ENABLE_COVERAGE)
  target_compile_options(clangVerify PRIVATE
    -fprofile-instr-generate -fcoverage-mapping)
  if(TARGET obj.clangVerify)
    target_compile_options(obj.clangVerify PRIVATE
      -fprofile-instr-generate -fcoverage-mapping)
  endif()
endif()

if(CPPVERIFY_SANITIZER)
  target_compile_options(clangVerify PRIVATE ${_cppverify_sanitize_flags})
  if(TARGET obj.clangVerify)
    target_compile_options(obj.clangVerify PRIVATE ${_cppverify_sanitize_flags})
  endif()
endif()

target_include_directories(clangVerify PUBLIC
  ${CMAKE_CURRENT_SOURCE_DIR}
  ${CMAKE_CURRENT_SOURCE_DIR}/Driver
  ${CMAKE_CURRENT_SOURCE_DIR}/../..
  )