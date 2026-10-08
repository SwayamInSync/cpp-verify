// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --check-ub %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Layer-A UB: preconditions that bound the operands discharge the overflow
// obligation.
int add(int a, int b)
  cppverify::pre(a >= 0 && a <= 1000 && b >= 0 && b <= 1000)
  cppverify::post(cppverify::result == a + b)
{
  return a + b;
}
// VERIFY: Verified: add
