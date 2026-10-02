// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Heap: p[i] subscript syntax (read and write), with disjointness over bounded
// indices.
spec bool valid(int *p, int n) { return true; }

void s(int* p, int i, int j, int v)
  pre(valid(p, 1000) && i != j && 0 <= i && i < 1000 && 0 <= j && j < 1000 && p[j] == 5)
  modifies(*p)
  post(p[i] == v && p[j] == 5)
{ p[i] = v; }
// VERIFY: Verified: s
