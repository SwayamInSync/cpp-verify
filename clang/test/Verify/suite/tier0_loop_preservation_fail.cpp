// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Tier-0: the invariant holds on entry (j == 0) but the body breaks it, so
// preservation (checked from an arbitrary state satisfying the invariant) fails.
int preservation_fail(int n)
  cppverify::pre(n >= 0 && n <= 10)
  cppverify::post(cppverify::result >= 0)
{
  int i = 0;
  int j = 0;
  while (i < n)
    cppverify::invariant(j == 0 && i >= 0 && i <= n)
    cppverify::decreases(n - i)
  {
    j = 1;
    i = i + 1;
  }
  return i;
}
// VERIFY: verification failed
