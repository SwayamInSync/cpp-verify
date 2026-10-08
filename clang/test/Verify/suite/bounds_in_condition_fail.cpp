// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify --check-ub %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY
// Array-bounds UB: an out-of-bounds read inside an if-condition is still checked.
cppverify::spec bool valid(int* p, int n) { return true; }
int g(int* p, int n, int i) cppverify::pre(valid(p, n) && 0 <= i && i < n) cppverify::post(true) { if (p[i + 5] > 0) return 1; return 0; }
// VERIFY: verification failed
