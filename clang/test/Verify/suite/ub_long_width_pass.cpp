// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --check-ub %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Layer-A UB: 2e9 + 2e9 = 4e9 overflows int32 but fits int64. Verifying this --
// including the 4-billion literal in the post -- proves long is modeled at 64-bit.
long sum(long a, long b)
  pre(a == 2000000000 && b == 2000000000)
  post(result == 4000000000)
{
  return a + b;
}
// VERIFY: Verified: sum
