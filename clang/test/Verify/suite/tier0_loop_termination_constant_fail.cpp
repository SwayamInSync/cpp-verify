// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Tier-0: the decreases measure must strictly decrease each iteration. A
// constant measure does not, so termination fails.
int termination_constant_fail(int n)
  pre(n >= 0 && n <= 5)
  post(result == n)
{
  int i = 0;
  while (i < n)
    invariant(0 <= i && i <= n)
    decreases(5)
  {
    i = i + 1;
  }
  return i;
}
// VERIFY: verification failed
