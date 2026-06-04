// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify --check-ub %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Array-bounds UB: writing p[i] with no upper bound on i is out of bounds.
spec bool valid(int* p, int n) { return true; }
void set(int* p, int n, int i, int v) pre(valid(p, n) && i >= 0) modifies(*p) post(p[i] == v) { p[i] = v; }
// VERIFY: verification failed
