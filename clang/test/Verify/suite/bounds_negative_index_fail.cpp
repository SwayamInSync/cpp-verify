// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify --check-ub %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Array-bounds UB: with only i < n (no lower bound), i can be negative.
spec bool valid(int* p, int n) { return true; }
int g(int* p, int n, int i) pre(valid(p, n) && i < n) post(result == p[i]) { return p[i]; }
// VERIFY: verification failed
