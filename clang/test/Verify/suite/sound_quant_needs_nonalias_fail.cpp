// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// A quantified post that only holds when two buffers alias must fail: without a
// non-aliasing/overlap precondition the store to d may clobber s.
void f(int* d, int* s, int n) pre(d != nullptr && s != nullptr && n >= 1 && n <= 100 && forall(i, 0, n, s[i] == 1)) modifies(*d) post(forall(i, 0, n, s[i] == 1)) { int j = 0; while (j < n) invariant(0 <= j && j <= n) decreases(n - j) { d[j] = 0; j = j + 1; } }
// VERIFY: verification failed
