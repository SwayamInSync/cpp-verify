// RUN: %cpp-verify --jobs=1 %s -- 2>&1 | FileCheck %s
// RUN: not %cpp-verify --jobs=1 %s -- -DUSER_ABS 2>&1 | FileCheck %s --check-prefix=USER
//
// std::abs of a long is libc++'s global abs(long) from <stdlib.h>, brought
// into std by <cstdlib>, where libstdc++ defines it in std itself: either is
// the absolute value. A global abs of the user's own is not.

#ifndef USER_ABS
#include "Inputs/global_abs.h"

long distance(long a, long b)
  cppverify::pre(-1000000 <= a && a <= 1000000 && -1000000 <= b && b <= 1000000)
  cppverify::post(cppverify::result == (a < b ? b - a : a - b))
{
  return std::abs(a - b);
}
// CHECK: Verified: distance [backend=z3]

long long magnitude(long long x)
  cppverify::pre(x > -9223372036854775807LL)
  cppverify::post(cppverify::result >= 0)
{
  return abs(x);
}
// CHECK: Verified: magnitude [backend=z3]
#else
// Not the absolute value: modeled as one, magnitude would verify.
long abs(long x) { return x; }

long magnitude(long x)
  cppverify::pre(x > -9223372036854775807L)
  cppverify::post(cppverify::result >= 0)
{
  return abs(x);
}
// USER-NOT: Verified: magnitude
#endif
