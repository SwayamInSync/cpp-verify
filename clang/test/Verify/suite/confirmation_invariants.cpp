// RUN: not %cpp-verify --jobs=4 --timeout=5000 --time-report %s -- 2>&1 | FileCheck %s
//
// Unrolling drops the loops' invariants and measures, so a failure of one
// has no copy at any bound: once the loops are unrolled once and no copy
// has appeared, the search for an execution that fails it stops, instead of
// solving every check at every bound until its time runs out (6.5 s at
// --timeout=5000 for this function, 31 s at the default 30000).

namespace cv = cppverify;

cv::spec bool valid(const int *p, int n) { return true; }

void reversed_copy(const int *a, int *out, int n)
  cv::pre(n >= 0 && valid(a, n) && valid(out, n))
  cv::modifies(*out)
  cv::post(cv::forall(i, 0, n, out[i] == a[i]))
{
  int i = 0;
  while (i < n)
    cv::invariant(0 <= i && i <= n)
    cv::invariant(cv::forall(j, 0, i, out[j] == a[j]))
    cv::decreases(n - i)
  {
    out[i] = a[n - 1 - i];
    i = i + 1;
  }
}
// CHECK: verification failed: reversed_copy {{.*}}invariant-preserved
// CHECK: note: the counterexample's state at the loop at {{[0-9]+}}:3 is any state its invariants allow
// CHECK-NOT: fails this check
// CHECK: total  lowering   solving  induction  certification  confirmation  function
// CHECK-NEXT: {{ *[0-9.]+ +[0-9.]+ +[0-9.]+ +[0-9.]+ +[0-9.]+ +0\.[0-9]+}}  reversed_copy
