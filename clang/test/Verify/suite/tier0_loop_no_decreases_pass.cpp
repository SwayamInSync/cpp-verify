// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Tier-0: decreases is optional. Without it, establishment + preservation are
// still checked (partial correctness); only the termination obligation is
// dropped.
int partial(int n)
  pre(n >= 0 && n <= 10)
  post(result == n)
{
  int i = 0;
  while (i < n)
    invariant(0 <= i && i <= n)
  {
    i = i + 1;
  }
  return i;
}
// VERIFY: Verified: partial
