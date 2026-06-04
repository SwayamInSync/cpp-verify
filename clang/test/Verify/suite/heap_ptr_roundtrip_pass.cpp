// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Heap: a store through a pointer-arithmetic address round-trips.
int rt(int* p, int v) pre(p != nullptr) modifies(*p) post(result == v) { *(p + 3) = v; return *(p + 3); }
// VERIFY: Verified: rt
