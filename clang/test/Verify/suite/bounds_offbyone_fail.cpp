// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify --check-ub %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Array-bounds UB: p[n] is one past the end of a length-n buffer.
spec bool valid(int* p, int n) { return true; }
int last(int* p, int n) pre(valid(p, n) && n >= 1) post(result == p[n - 1]) { return p[n]; }
// VERIFY: verification failed
