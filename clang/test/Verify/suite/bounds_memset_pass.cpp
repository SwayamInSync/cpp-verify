// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --check-ub %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// memset: correct AND memory-safe in one proof (every p[j] write is in bounds).
spec bool valid(int* p, int n) { return true; }
void memset0(int* p, int n)
  pre(valid(p, n) && n >= 0 && n <= 1000)
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
