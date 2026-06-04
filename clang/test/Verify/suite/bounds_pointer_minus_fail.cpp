// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify --check-ub %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Array-bounds UB: *(p - 1) is before the start of the buffer.
spec bool valid(int* p, int n) { return true; }
int g(int* p, int n) pre(valid(p, n) && n >= 1) post(result == *(p - 1)) { return *(p - 1); }
// VERIFY: verification failed
