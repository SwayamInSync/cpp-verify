// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify --check-ub %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Array-bounds UB: p[i + 1] is out of bounds when i + 1 reaches n.
spec bool valid(int* p, int n) { return true; }
int g(int* p, int n, int i) pre(valid(p, n) && 0 <= i && i < n) post(result == p[i + 1]) { return p[i + 1]; }
// VERIFY: verification failed
