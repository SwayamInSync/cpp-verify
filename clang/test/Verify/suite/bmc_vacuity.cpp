// RUN: not %cpp-verify --backend=bmc --unroll=3 %s -- 2>&1 | FileCheck %s
//
// A bounded proof that no execution reaches says nothing, as Kani reports
// an unreachable check: under BMC the vacuity checks run on the program
// unrolled to the bound, where an execution that would run a loop past it
// ends.

int impossible(int x)
  cppverify::pre(x > 0 && x < 0)
  cppverify::post(cppverify::result == 42)
{
  return 0;
}
// CHECK-DAG: Verified: impossible [backend=bmc, bound=0] [vacuous]
// CHECK-DAG: warning: impossible: the precondition is unsatisfiable

// Every execution runs the loop at least 100 times.
int long_loop(int n)
  cppverify::pre(n >= 100 && n <= 200)
  cppverify::post(cppverify::result == n)
{
  int i = 0;
  while (i < n)
    cppverify::invariant(0 <= i && i <= n)
    cppverify::decreases(n - i)
  {
    i = i + 1;
  }
  return i;
}
// CHECK-DAG: BoundedSafe: long_loop [backend=bmc, bound=3] {{.*}}[vacuous]
// CHECK-DAG: warning: long_loop: no execution finishes within 3 loop iterations

int short_loop(int n)
  cppverify::pre(n >= 0 && n <= 2)
  cppverify::post(cppverify::result == n)
{
  int i = 0;
  while (i < n)
    cppverify::invariant(0 <= i && i <= n)
    cppverify::decreases(n - i)
  {
    i = i + 1;
  }
  return i;
}
// CHECK-DAG: Verified: short_loop [backend=bmc, bound=2]
// CHECK-NOT: short_loop: no execution
