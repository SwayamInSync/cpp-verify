// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --check-ub %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY
// Layer-A UB: ruling out INT_MIN makes negation safe.
int abs(int x)
  cppverify::pre(x > -2147483648)
  cppverify::post(cppverify::result >= 0)
{
  return x < 0 ? -x : x;
}
// VERIFY: Verified: abs
