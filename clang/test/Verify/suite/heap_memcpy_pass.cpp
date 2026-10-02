// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Heap: memcpy verifies end-to-end -- a two-buffer copy loop whose quantified
// invariant is preserved across stores, using the non-overlap default: the
// two buffers are distinct objects.
spec bool valid(int *p, int n) { return true; }

void mcpy(int* d, int* s, int n)
  pre(valid(d, n) && valid(s, n) && n >= 0 && n <= 1000)
  modifies(*d)
  post(forall(i, 0, n, d[i] == s[i]))
{
  int j = 0;
  while (j < n)
    invariant(0 <= j && j <= n && forall(i, 0, j, d[i] == s[i]))
    decreases(n - j)
  { d[j] = s[j]; j = j + 1; }
}
// VERIFY: Verified: mcpy
