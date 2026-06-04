// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Off-by-one: the body establishes [0, j) but the invariant claims [0, j], which
// is not yet true for the cell at j -- preservation must fail.
void f(int* p, int n) pre(p != nullptr && n >= 1 && n <= 100) modifies(*p) post(forall(i, 0, n, p[i] == 0)) { int j = 0; while (j < n) invariant(0 <= j && j <= n && forall(i, 0, j + 1, p[i] == 0)) decreases(n - j) { p[j] = 0; j = j + 1; } }
// VERIFY: verification failed
