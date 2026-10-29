// RUN: not %python %S/Inputs/within_seconds.py 40 %cpp-verify --jobs=1 --timeout=60000 %s -- 2>&1 | FileCheck %s
// RUN: not %python %S/Inputs/within_seconds.py 40 %cpp-verify --jobs=3 --timeout=60000 %s -- 2>&1 | FileCheck %s
//
// The complete query refutes the function at once, through the second check,
// while the solver's search for the first check's own counterexample, a
// solution of Fermat's equation for cubes, does not end within the timeout.
// The obligations then only choose the failure to report, within the
// complete query's probe, so the second check is reported well within 40 s,
// where waiting for the first takes the 60 s timeout.
//
// Any build of Z3 refutes a < 0 at once and none settles the cubes. The test
// used to fail a postcondition whose own query does not end and which the
// complete query refuted within the probe only with a Z3 built by GCC: with
// one built by Clang, as the release's is, it took the 60 s path.

void cubes(int a, int b, int c)
  cppverify::pre(0 < a && a < 1000 && 0 < b && b < 1000 && 0 < c && c < 1000)
{
  cppverify::check(a * a * a + b * b * b != c * c * c);
  cppverify::check(a < 0);
}
// CHECK: :[[@LINE-2]]:22: error: verification failed: cubes [assertion] {{.*}}[reason=counterexample]
// CHECK-NOT: within_seconds
