// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Tier-0: the invariant must hold when the loop is first reached. Here i == 5
// is false on entry (i == 0), so establishment fails.
int establishment_fail(int n)
  pre(n >= 0 && n <= 5)
  post(result >= 0)
{
  int i = 0;
  while (i < n)
    invariant(i == 5)
    decreases(n - i)
  {
    i = i + 1;
  }
  return i;
}
// VERIFY: verification failed
