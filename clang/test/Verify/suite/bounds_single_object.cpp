// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=CHECKED
// RUN: %cpp-verify --no-check-ub %s 2>&1 | FileCheck %s --check-prefix=UNCHECKED
// Without a valid(p, n) declaration a pointer addresses a single object, so
// p[i] is in bounds only at i == 0. --no-check-ub turns memory checking off.
int get(int* p, int i) cppverify::pre(p != nullptr && i >= 0) cppverify::post(cppverify::result == p[i]) { return p[i]; }
// CHECKED: error: verification failed: get [{{.*}}::bounds@
// UNCHECKED: Verified: get

int first(int* p) cppverify::pre(p != nullptr) cppverify::post(cppverify::result == p[0]) { return p[0]; }
// CHECKED: Verified: first
