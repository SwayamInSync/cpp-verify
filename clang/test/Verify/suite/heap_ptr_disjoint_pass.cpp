// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY
// Heap: storing at p+k does not disturb p+i when i != k (array theory over
// integer addresses). Indices are bounded, as in real buffer code.
cppverify::spec bool valid(int *p, int n) { return true; }

void d(int* p, int i, int k, int v)
  cppverify::pre(valid(p, 1000) && i != k && 0 <= i && i < 1000 && 0 <= k && k < 1000)
  cppverify::modifies(*p)
  cppverify::post(*(p + i) == cppverify::old(*(p + i)))
{ *(p + k) = v; }
// VERIFY: Verified: d
