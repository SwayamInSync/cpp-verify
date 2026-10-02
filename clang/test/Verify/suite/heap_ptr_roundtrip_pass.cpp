// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Heap: a store through a pointer-arithmetic address round-trips.
spec bool valid(int *p, int n) { return true; }

int rt(int* p, int v) pre(valid(p, 4)) modifies(*p) post(result == v) { *(p + 3) = v; return *(p + 3); }
// VERIFY: Verified: rt
