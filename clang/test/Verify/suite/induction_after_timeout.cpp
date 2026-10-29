// RUN: not %cpp-verify --jobs=1 --timeout=2000 %s -- 2>&1 | FileCheck %s
//
// A lemma the solver cannot settle is tried by induction, as one whose
// claim needs unbounded unfolding is: adjacent order gives every order by
// induction on the second index, which the solver alone does not find.

namespace cv = cppverify;

cv::proof void ordered(const int *a, int n, int i, int j)
  cv::pre(cv::valid(a, n))
  cv::pre(cv::forall(k, 1, n, a[k - 1] <= a[k]))
  cv::pre(0 <= i && i <= j && j < n)
  cv::post(a[i] <= a[j])
{
}
// CHECK-DAG: Verified: ordered [backend=z3] [by induction on j]

// A false lemma fails as before: its counterexample comes first.
cv::proof void strictly(const int *a, int n, int i, int j)
  cv::pre(cv::valid(a, n))
  cv::pre(cv::forall(k, 1, n, a[k - 1] <= a[k]))
  cv::pre(0 <= i && i < j && j < n)
  cv::post(a[i] < a[j])
{
}
// CHECK-DAG: error: verification failed: strictly [postcondition]

// Induction is a proof of a lemma: an executable function is not tried.
int ordered_exec(const int *a, int n, int i, int j)
  cv::pre(cv::valid(a, n))
  cv::pre(cv::forall(k, 1, n, a[k - 1] <= a[k]))
  cv::pre(0 <= i && i <= j && j < n)
  cv::post(a[i] <= a[j])
{
  return 0;
}
// CHECK-DAG: Unresolved: ordered_exec [backend=z3] [reason=solver.timeout]
