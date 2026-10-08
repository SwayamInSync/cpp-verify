// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY
// Tier-0: a straightforward counting loop with an inductive invariant and a
// well-founded measure verifies (establishment + preservation + termination).
int count_up(int n)
  cppverify::pre(n >= 0 && n <= 100)
  cppverify::post(cppverify::result == n)
{
  int i = 0;
  while (i < n)
    cppverify::invariant(0 <= i && i <= n)
    cppverify::decreases(n - i)
  {
    i = i + 1;
  }
  return i;
}
// VERIFY: Verified: count_up
