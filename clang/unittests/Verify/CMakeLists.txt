include(${CMAKE_CURRENT_SOURCE_DIR}/../../cmake/modules/CppVerifyZ3.cmake)
cppverify_ensure_z3()
if(NOT CPPVERIFY_Z3_TARGET OR NOT TARGET clangVerify)
  return()
endif()

add_distinct_clang_unittest(VerifyTests
  CertifyTest.cpp
  EncodingParityTest.cpp
  MachineIntegerEncodingTest.cpp
  CLANG_LIBS
  clangVerify
  LINK_LIBS
  ${CPPVERIFY_Z3_TARGET}
  LLVM_COMPONENTS
  Support
  )
