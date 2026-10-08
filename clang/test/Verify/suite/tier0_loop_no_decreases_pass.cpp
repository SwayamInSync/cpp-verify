// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY
// Tier-0: decreases(*) lets a loop diverge. Establishment and preservation
// are still checked, and the verdict is partial correctness: it covers the
// executions that terminate.
int partial(int n)
  cppverify::pre(n >= 0 && n <= 10)
  cppverify::post(cppverify::result == n)
{
  int i = 0;
  while (i < n)
    cppverify::invariant(0 <= i && i <= n)
    cppverify::decreases(*)
  {
    i = i + 1;
  }
  return i;
}
// VERIFY: Verified: partial [backend=z3] [partial]
// VERIFY: warning: partial: proved only for executions that terminate: cppverify::decreases(*) at 13:26 allows it to diverge
