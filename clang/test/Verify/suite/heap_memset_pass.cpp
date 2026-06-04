// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Heap: memset zeroes a buffer; the quantified loop invariant (over a symbolic
// range) is preserved across stores and establishes the quantified post.
void memset0(int* p, int n)
  pre(p != nullptr && n >= 0 && n <= 1000)
  modifies(*p)
  post(forall(i, 0, n, p[i] == 0))
{
  int j = 0;
  while (j < n)
    invariant(0 <= j && j <= n && forall(i, 0, j, p[i] == 0))
    decreases(n - j)
  { p[j] = 0; j = j + 1; }
}
// VERIFY: Verified: memset0
