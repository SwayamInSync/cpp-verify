// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify --check-ub %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Layer-A UB: long arithmetic is checked at 64-bit (target data model).
long add(long a, long b)
  post(result == a + b)
{
  return a + b;
}
// VERIFY: verification failed
