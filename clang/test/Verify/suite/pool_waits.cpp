// RUN: not %python %S/Inputs/within_seconds.py 60 %cpp-verify --jobs=2 --timeout=20000 --function-timeout=8000 %s -- 2>&1 | FileCheck %s
// RUN: not %python %S/Inputs/within_seconds.py 60 %cpp-verify --jobs=3 --timeout=20000 --function-timeout=8000 %s -- 2>&1 | FileCheck %s
// RUN: not %python %S/Inputs/at_least_seconds.py 6 %cpp-verify --jobs=2 --timeout=20000 --function-timeout=3000 %s -- -DTHREE 2>&1 | FileCheck %s --check-prefix=THREE

// A worker that waits for its function's obligations runs only those. The
// spec's reads check and post check are two queries of one function: had its
// worker taken up a query of cubes or fourth_powers between them, the post
// check would have found the function's time spent, not its counterexample.

cppverify::spec int first_or_second(const int *p, bool second)
  cppverify::reads(p, 2)
  cppverify::post(cppverify::result > 0)
{
  return second ? p[1] : p[0];
}
// CHECK: Verified: spec reads: first_or_second
// CHECK-NEXT: error: spec post failed: first_or_second {{.*}}[reason=counterexample]

// No solver settles these within the function's time.
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

// --jobs=2 runs two functions at once, whichever thread waits: three that
// take their 3 s each take at least 6 s.
#ifdef THREE
cppverify::proof void fifth_powers(int x, int y, int z)
  cppverify::pre(x > 0 && y > 0 && z > 0)
  cppverify::post(x * x * x * x * x + y * y * y * y * y != z * z * z * z * z)
  cppverify::post(x * x * x * x * x + y * y * y * y * y != z * z * z * z * z + 0)
{
}
#endif
// THREE: Unresolved: fifth_powers
// THREE-NOT: at_least_seconds
