// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --check-ub %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Layer-A UB inside a loop: an invariant that bounds the accumulator discharges
// the per-iteration overflow obligation.
int count_up(int n)
  pre(n >= 0 && n <= 1000)
  post(result == n)
{
  int i = 0;
  while (i < n)
    invariant(0 <= i && i <= n)
    decreases(n - i)
  {
    i = i + 1;
  }
  return i;
}
// VERIFY: Verified: count_up
