// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify --check-ub %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Array-bounds UB: reading p[i] with no upper bound on i is out of bounds.
cppverify::spec bool valid(int* p, int n) { return true; }
int get(int* p, int n, int i) cppverify::pre(valid(p, n) && i >= 0) cppverify::post(cppverify::result == p[i]) { return p[i]; }
// VERIFY: verification failed
