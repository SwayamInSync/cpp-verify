// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// A forall over a SYMBOLIC range that is false must fail (stores 5, claims 0).
void f(int* p, int n) pre(p != nullptr && n >= 1 && n <= 100) modifies(*p) post(forall(i, 0, n, p[i] == 0)) { int j = 0; while (j < n) invariant(0 <= j && j <= n && forall(i, 0, j, p[i] == 5)) decreases(n - j) { p[j] = 5; j = j + 1; } }
// VERIFY: verification failed
