// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify --check-ub %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Layer-A UB: unbounded signed addition can overflow (INT_MAX + 1 is UB).
int add(int a, int b)
  post(result == a + b)
{
  return a + b;
}
// VERIFY: verification failed
