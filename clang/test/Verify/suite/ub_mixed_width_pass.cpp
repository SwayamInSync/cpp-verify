// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --check-ub %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Layer-A UB: mixed int/long arithmetic -- the int operand is sign-extended to
// 64 bits, so (long)a + b is checked (and verified) at 64-bit width.
long widen(int a, long b)
  pre(b >= 0 && b <= 1000)
  post(result == (long)a + b)
{
  return (long)a + b;
}
// VERIFY: Verified: widen
