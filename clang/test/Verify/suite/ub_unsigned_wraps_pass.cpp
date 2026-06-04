// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --check-ub %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Layer-A UB: unsigned overflow is DEFINED (modular wraparound) in C++, so no
// obligation is emitted -- this verifies with no bounds on a, b.
unsigned uadd(unsigned a, unsigned b)
  post(result == a + b)
{
  return a + b;
}
// VERIFY: Verified: uadd
