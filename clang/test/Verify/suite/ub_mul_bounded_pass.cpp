// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --check-ub %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY
// Layer-A UB: |x| <= 46340 keeps x*x below INT_MAX, so multiplication is safe.
int square(int x)
  cppverify::pre(x >= -46340 && x <= 46340)
  cppverify::post(cppverify::result >= 0)
{
  return x * x;
}
// VERIFY: Verified: square
