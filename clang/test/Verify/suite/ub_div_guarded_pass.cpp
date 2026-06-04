// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --check-ub %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Layer-A UB: b > 0 rules out both division by zero and the INT_MIN / -1 case.
int dv(int a, int b)
  pre(b > 0)
  post(result == 0)
{
  int q = a / b;
  return 0;
}
// VERIFY: Verified: dv
