// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Tier-0: nested loops. The inner loop's modified variable is havocked within
// the outer loop body; both invariants are inductive and both measures
// well-founded.
int nested(int n)
  pre(n >= 0 && n <= 20)
  post(result == n)
{
  int total = 0;
  int i = 0;
  while (i < n)
    invariant(0 <= i && i <= n && total == i)
    decreases(n - i)
  {
    int j = 0;
    while (j < 1)
      invariant(0 <= j && j <= 1)
      decreases(1 - j)
    {
      j = j + 1;
    }
    total = total + 1;
    i = i + 1;
  }
  return total;
}
// VERIFY: Verified: nested
