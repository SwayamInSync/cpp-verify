// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Heap soundness: storing through *b is a frame violation when only *a is in modifies.
void f(int* a, int* b, int v) pre(a != nullptr && b != nullptr) modifies(*a) post(true) { *b = v; }
// VERIFY: verification failed
