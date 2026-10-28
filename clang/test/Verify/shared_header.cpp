// RUN: not %cpp-verify --jobs=1 %s -- -I %S/Inputs 2>&1 | FileCheck %s --implicit-check-not=error:
// RUN: %clang_cc1 -std=c++11 -fsyntax-only -Wall -Wextra -pedantic -verify -I %S/Inputs %s
// RUN: %clang_cc1 -std=c++17 -fverify-contracts -fsyntax-only -verify -I %S/Inputs %s
// RUN: %clang_cc1 -std=c++17 -fverify-contracts -fno-verify -emit-llvm -o - -I %S/Inputs %s | FileCheck %s --check-prefix=IR
//
// A header shared with compilers that do not know the constructs guards them
// with __cppverify__: this compiler verifies the contracts, and any other
// compiler, or this one without -fverify-contracts, reads plain C++.

#include "shared_header.h"

int use(int x)
{
  return clamp(x, 0, 10) + double_by_steps(3) + halve(x);
}

// expected-no-diagnostics

// CHECK-DAG: Verified: clamp
// CHECK-DAG: Verified: double_by_steps
// CHECK-DAG: shared_header.h:44:{{[0-9]+}}: error: verification failed: halve

// IR: define {{.*}} @_Z3usei(
// IR-NOT: twice
