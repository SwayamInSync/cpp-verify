// RUN: not %clang_cc1 -std=c++17 -fverify-contracts -emit-llvm -o - %s 2>&1 | FileCheck %s
// RUN: %clang_cc1 -std=c++17 -fverify-contracts -fno-verify -emit-llvm -o - %s | FileCheck %s --check-prefix=SKIPPED
//
// A compilation verifies before it generates IR, never beside it: IR
// generation fills caches of the ASTContext and the SourceManager that the
// verifier reads. A failure therefore stops the compilation before any IR.

int next(int x)
  cppverify::post(cppverify::result > x)
{
  return x;
}

// CHECK: compile_verifies_first.cpp:9:37: error: verification failed: next [postcondition]
// CHECK-NOT: define

// SKIPPED: define {{.*}} @_Z4nexti(
