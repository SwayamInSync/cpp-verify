// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify --check-ub %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY
// Array-bounds UB: the loop runs to j == n and writes p[n], one past the end.
cppverify::spec bool valid(int* p, int n) { return true; }
void fill(int* p, int n) cppverify::pre(valid(p, n) && n >= 1 && n <= 1000) cppverify::modifies(*p) cppverify::post(true) { int j = 0; while (j <= n) cppverify::invariant(0 <= j && j <= n + 1) cppverify::decreases(n + 1 - j) { p[j] = 0; j = j + 1; } }
// VERIFY: verification failed
