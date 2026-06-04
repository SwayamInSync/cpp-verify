// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --check-ub %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Layer-A UB: the overflow obligation for x + 1 is path-guarded. The early
// return excludes x == INT_MAX, so x + 1 is only reached when it is safe.
int inc(int x)
  post(result >= x)
{
  if (x >= 2147483647)
    return x;
  return x + 1;
}
// VERIFY: Verified: inc
