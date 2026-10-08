// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --check-ub %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY
// Layer-A UB: unsigned overflow is DEFINED (modular wraparound) in C++, so no
// obligation is emitted -- this verifies with no bounds on a, b. Contract
// arithmetic is mathematical, so the contract states the wraparound.
unsigned uadd(unsigned a, unsigned b)
  cppverify::post(cppverify::result == (a + b) % 4294967296)
{
  return a + b;
}
// VERIFY: Verified: uadd
