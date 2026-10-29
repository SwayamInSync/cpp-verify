// RUN: not %cpp-verify --jobs=1 %s -- -I %S/Inputs 2>&1 | FileCheck %s --implicit-check-not=error:
// RUN: %clang_cc1 -std=c++11 -fsyntax-only -Wall -Wextra -pedantic -verify -I %S/Inputs %s
// RUN: %clang_cc1 -std=c++17 -fverify-contracts -fsyntax-only -verify -I %S/Inputs %s
// RUN: %clang_cc1 -std=c++17 -fverify-contracts -fno-verify -emit-llvm -o - -I %S/Inputs %s | FileCheck %s --check-prefix=IR
// RUN: not %cpp-verify --jobs=1 --diagnostics-format=json %s -- -I %S/Inputs | FileCheck %s --check-prefix=JSON
//
// A header shared with compilers that do not know the constructs guards them
// with __cppverify__: this compiler verifies the contracts, and any other
// compiler, or this one without -fverify-contracts, reads plain C++. A failure
// in a macro's argument is shown where the argument is written, and one in a
// macro's body where the macro is used, as Clang shows its own errors.

#include "shared_header.h"

int use(int x)
{
  return clamp(x, 0, 10) + double_by_steps(3) + halve(x) + decrement(x);
}

// expected-no-diagnostics

// CHECK-DAG: Verified: clamp
// CHECK-DAG: Verified: double_by_steps
// CHECK-DAG: shared_header.h:44:51: error: verification failed: halve [postcondition]
// CHECK-DAG: shared_header.h:5:24: note: expanded from macro 'CPPVERIFY'
// CHECK-DAG: shared_header.h:44:51: note: counterexample: x = -1, result = 0
// CHECK-DAG: shared_header.h:56:3: error: verification failed: decrement [postcondition]
// CHECK-DAG: shared_header.h:50:55: note: expanded from macro 'NONNEGATIVE'

// JSON-DAG: "function":"halve",{{.*}}"obligation":{"id":"{{[^"]*}}::postcondition@44:51",{{.*}}"source":{"column":29,"end_column":55,"end_line":44,"file":"{{[^"]*}}shared_header.h","line":44}
// JSON-DAG: "function":"decrement",{{.*}}"source":{"column":3,"end_column":14,"end_line":56,"file":"{{[^"]*}}shared_header.h","line":56}

// IR: define {{.*}} @_Z3usei(
// IR-NOT: twice
