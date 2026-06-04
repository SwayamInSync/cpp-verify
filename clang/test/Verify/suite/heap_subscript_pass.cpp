// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Heap: p[i] subscript syntax (read and write), with disjointness.
void s(int* p, int i, int j, int v) pre(p != nullptr && i != j && p[j] == 5) modifies(*p) post(p[i] == v && p[j] == 5) { p[i] = v; }
// VERIFY: Verified: s
