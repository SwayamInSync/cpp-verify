// RUN: not %python %S/Inputs/within_seconds.py 20 %cpp-verify --jobs=1 %s -- 2>&1 | FileCheck %s
//
// The search for an execution after a failure through a loop takes an
// attempt's time, not a query's. When that ends before the bound, the note
// keeps what the bounds before it settled.

namespace cv = cppverify;

int max_index(const int *a, int n)
  cv::pre(n > 0 && cv::valid(a, n))
  cv::post(0 <= cv::result && cv::result < n)
  cv::post(cv::forall(k, 0, n, a[k] <= a[cv::result]))
{
  int best = 0;
  for (int i = 1; i < n; ++i)
    cv::invariant(1 <= i && i <= n && 0 <= best && best < i)
    cv::decreases(n - i)
  {
    if (a[i] > a[best])
      best = i;
  }
  return best;
}

// CHECK: error: verification failed: max_index [postcondition] [backend=z3] [reason=counterexample]
// CHECK: note: the counterexample's state at the loop at 15:3 is any state its invariants allow
// CHECK-NEXT: note: no execution fails this check within {{[1-9]}} iteration{{s?}} of each loop; the search ran out of time there
// CHECK: Summary: 1 failed
