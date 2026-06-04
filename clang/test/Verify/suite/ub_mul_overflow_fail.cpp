// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify --check-ub %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Layer-A UB: unbounded signed multiplication overflows.
int square(int x)
  post(result >= 0)
{
  return x * x;
}
// VERIFY: verification failed
