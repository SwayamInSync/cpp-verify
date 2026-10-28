// RUN: not %cpp-verify --jobs=4 --timeout=20000 --time-report %s -- 2>&1 | FileCheck %s
//
// Unrolling drops the loops' invariants and measures, so a failure of one
// has no copy at any bound: once the loops are unrolled once and no copy
// has appeared, the search for an execution that fails it stops, instead of
// solving every check at every bound until its time runs out (5.8 s at
// --timeout=5000 for this function, 30 s at the default 30000). The time
// report shows the confirmation under a second; the budget leaves the
// failure itself time on a slow core (at --timeout=5000 a macOS runner timed
// out before finding it).

namespace cv = cppverify;

cv::spec bool valid(const int *p, int n) { return true; }

// The copy is right; the first invariant's bound on i is not, and only an
// invariant states it.
void bounded_copy(const int *a, int *out, int n)
  cv::pre(n >= 0 && valid(a, n) && valid(out, n))
  cv::modifies(*out)
  cv::post(cv::forall(i, 0, n, out[i] == a[i]))
{
  int i = 0;
  while (i < n)
    cv::invariant(0 <= i && i <= n && i <= 8)
    cv::invariant(cv::forall(j, 0, i, out[j] == a[j]))
    cv::decreases(n - i)
  {
    out[i] = a[i];
    i = i + 1;
  }
}
// CHECK: verification failed: bounded_copy {{.*}}invariant-preserved
// CHECK: note: the counterexample's state at the loop at {{[0-9]+}}:3 is any state its invariants allow
// CHECK-NOT: fails this check
// CHECK: total  lowering   solving  induction  certification  confirmation  function
// CHECK-NEXT: {{ *[0-9.]+ +[0-9.]+ +[0-9.]+ +[0-9.]+ +[0-9.]+ +0\.[0-9]+}}  bounded_copy
