// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify --check-ub %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Layer-A UB: division with no precondition on the divisor can divide by zero.
int dv(int a, int b)
  post(result == 0)
{
  int q = a / b;
  return 0;
}
// VERIFY: verification failed
