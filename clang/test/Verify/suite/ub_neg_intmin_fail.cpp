// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify --check-ub %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Layer-A UB: negating INT_MIN overflows. abs() without a guard is unsafe.
int abs(int x)
  post(result >= 0)
{
  return x < 0 ? -x : x;
}
// VERIFY: verification failed
