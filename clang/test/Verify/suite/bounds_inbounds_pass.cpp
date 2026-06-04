// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --check-ub %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Array-bounds: a read and a write within [0, n) are in bounds.
spec bool valid(int* p, int n) { return true; }
int rw(int* p, int n, int i, int v) pre(valid(p, n) && 0 <= i && i < n) modifies(*p) post(p[i] == v) { p[i] = v; return p[i]; }
// VERIFY: Verified: rw
