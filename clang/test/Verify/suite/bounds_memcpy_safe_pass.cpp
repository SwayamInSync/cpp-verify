// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --check-ub %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// memcpy is provably memory-safe: every d[j] write and s[j] read is in bounds.
// (Its functional correctness is verified separately; see heap_memcpy_pass.)
spec bool valid(int* p, int n) { return true; }
void mcpy(int* d, int* s, int n)
  pre(valid(d, n) && valid(s, n) && n >= 0 && n <= 1000)
  modifies(*d)
  post(true)
{
  int j = 0;
  while (j < n) invariant(0 <= j && j <= n) decreases(n - j) { d[j] = s[j]; j = j + 1; }
}
// VERIFY: Verified: mcpy
