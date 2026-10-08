// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify --check-ub %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Array-bounds UB across a call: the caller passes index 100 but cannot establish
// 100 < n (it only knows n >= 1), so the callee's precondition fails at the call.
cppverify::spec bool valid(int* p, int n) { return true; }
int get(int* p, int n, int i) cppverify::pre(valid(p, n) && 0 <= i && i < n) cppverify::post(cppverify::result == p[i]) { return p[i]; }
int caller(int* p, int n) cppverify::pre(valid(p, n) && n >= 1) cppverify::post(true) { return get(p, n, 100); }
// VERIFY: verification failed
