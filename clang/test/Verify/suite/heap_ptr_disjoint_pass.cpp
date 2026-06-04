// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Heap: storing at p+k does not disturb p+i when i != k (array theory over BV addresses).
void d(int* p, int i, int k, int v) pre(p != nullptr && i != k) modifies(*p) post(*(p + i) == old(*(p + i))) { *(p + k) = v; }
// VERIFY: Verified: d
