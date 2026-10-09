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

# A vendored Z3 installs its headers when its ExternalProject builds, so the
# sources that include them must wait for it (DEPENDS orders obj.clangVerify).
get_property(_cppverify_z3_ep GLOBAL PROPERTY CPPVERIFY_Z3_EP_TARGET)

add_clang_library(clangVerify
  IR/VExpr.cpp
  IR/VStmt.cpp
  Frontend/ASTConverter.cpp
  Transform/Passivize.cpp
  Transform/Inductive.cpp
  Transform/Origins.cpp
  Transform/Ownership.cpp
  Transform/LoopUnroll.cpp
  Transform/SpecInline.cpp
  Transform/UBChecks.cpp
  Backend/Certify.cpp
  Backend/Presburger.cpp
  Backend/Obligation.cpp
  Backend/Induction.cpp
  Backend/ObligationSimplify.cpp
  Backend/ObligationSerialization.cpp
  Backend/ProofCache.cpp
  Backend/CVC5Backend.cpp
  Backend/Z3Encode.cpp
  Backend/SpecAxioms.cpp
  Backend/VerifyBackend.cpp
  Backend/LeanBackend.cpp
  Driver/Verifier.cpp
  Driver/DumpIR.cpp
  Driver/CppVerifyIntegration.cpp
  Driver/CppVerifyVersion.cpp

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

set(CPPVERIFY_VERSION 0.2.0-dev)
get_property(_cppverify_z3_origin GLOBAL PROPERTY CPPVERIFY_Z3_ORIGIN)
set_property(SOURCE Driver/CppVerifyVersion.cpp APPEND PROPERTY COMPILE_DEFINITIONS
  CPPVERIFY_VERSION="${CPPVERIFY_VERSION}"
  CPPVERIFY_Z3_ORIGIN="${_cppverify_z3_origin}")

if(CPPVERIFY_ENABLE_COVERAGE)
  target_compile_options(clangVerify PRIVATE
    -fprofile-instr-generate -fcoverage-mapping)
  if(TARGET obj.clangVerify)
    target_compile_options(obj.clangVerify PRIVATE
      -fprofile-instr-generate -fcoverage-mapping)
  endif()
endif()
target_include_directories(clangVerify PUBLIC
  ${CMAKE_CURRENT_SOURCE_DIR}
  ${CMAKE_CURRENT_SOURCE_DIR}/Driver
  ${CMAKE_CURRENT_SOURCE_DIR}/../..
  )