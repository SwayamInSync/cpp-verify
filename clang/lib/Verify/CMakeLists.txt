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

add_clang_library(clangVerify
  IR/VExpr.cpp
  IR/VStmt.cpp
  Frontend/ASTConverter.cpp
  Transform/Passivize.cpp
  Backend/WPCalc.cpp
  Backend/Z3Encode.cpp
  Driver/Verifier.cpp
  Driver/DumpIR.cpp
  Driver/CppVerifyIntegration.cpp

  LINK_LIBS
  clangAST
  clangBasic
  clangFrontend
  clangLex
  clangSema

  DEPENDS
  intrinsics_gen
)

target_link_libraries(clangVerify PRIVATE ${CPPVERIFY_Z3_TARGET})
target_include_directories(clangVerify PUBLIC
  ${CMAKE_CURRENT_SOURCE_DIR}
  ${CMAKE_CURRENT_SOURCE_DIR}/Driver
  ${CMAKE_CURRENT_SOURCE_DIR}/../..
  )