// REQUIRES: cvc5
// RUN: not %python %S/Inputs/within_seconds.py 60 %cpp-verify --backend=cvc5 --jobs=2 --timeout=20000 --function-timeout=8000 %s -- 2>&1 | FileCheck %s

// pool_waits.cpp with cvc5, whose obligations are tasks too.

cppverify::spec int first_or_second(const int *p, bool second)
  cppverify::reads(p, 2)
  cppverify::post(cppverify::result > 0)
{
  return second ? p[1] : p[0];
}
// CHECK: Verified: spec reads: first_or_second
// CHECK-NEXT: error: spec post failed: first_or_second {{.*}}[reason=counterexample]

cppverify::proof void cubes(int x, int y, int z)
  cppverify::pre(x > 0 && y > 0 && z > 0)
  cppverify::post(x * x * x + y * y * y != z * z * z)
  cppverify::post(x * x * x + y * y * y != z * z * z + 0)
{
}

cppverify::proof void fourth_powers(int x, int y, int z)
  cppverify::pre(x > 0 && y > 0 && z > 0)
  cppverify::post(x * x * x * x + y * y * y * y != z * z * z * z)
  cppverify::post(x * x * x * x + y * y * y * y != z * z * z * z + 0)
{
}
