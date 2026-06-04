// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify --check-ub %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Layer-A UB: even with b != 0, INT_MIN / -1 overflows.
int dv(int a, int b)
  pre(b != 0)
  post(result == 0)
{
  int q = a / b;
  return 0;
}
// VERIFY: verification failed
