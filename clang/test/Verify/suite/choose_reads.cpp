// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s --implicit-check-not=Verified:
//
// The reads check of a spec follows the loads in the body of a choose it
// applies, at every value of the choice's binder, as Dafny checks the reads
// of a let-such-that. The choice itself reads nothing else.

namespace cv = cppverify;
using namespace cppverify;

cv::spec int index_of(const int *a, int n, int x)
  cv::reads(a, n)
{
  return cv::choose(k, 0, n, a[k] == x);
}
// CHECK-DAG: Verified: spec reads: index_of
// CHECK-DAG: Verified: spec axiom: index_of

// a[n] lies outside the declared cells.
cv::spec int index_past(const int *a, int n, int x)
  cv::reads(a, n)
{
  return cv::choose(k, 0, n + 1, a[k] == x);
}
// CHECK-DAG: error: spec reads failed: index_past [backend=z3] [reason=counterexample]
// CHECK-DAG: Verified: spec axiom: index_past

// Once the reads clause holds, a write outside it keeps the value.
void set_other(const int *a, int n, int *b, int x)
  cv::pre(valid(a, n) && n >= 1 && n <= 100 && valid(b, 1))
  cv::modifies(*b)
  cv::post(index_of(a, n, x) == cv::old(index_of(a, n, x)))
{
  cv::hide(index_of);
  *b = 5;
}
// CHECK-DAG: Verified: set_other [backend=z3]

cv::spec int count_to(const int *a, int n, int x)
  cv::reads(a, n)
  cv::decreases(n)
{
  return n <= 0 ? 0
                : cv::choose(k, 0, 2, k == (a[n - 1] == x ? 1 : 0)) +
                      count_to(a, n - 1, x);
}
// CHECK-DAG: Verified: spec reads: count_to
// CHECK-DAG: Verified: spec decreases: count_to

void set_other_rec(const int *a, int n, int *b, int x)
  cv::pre(valid(a, n) && n >= 1 && n <= 100 && valid(b, 1))
  cv::modifies(*b)
  cv::post(count_to(a, n, x) == cv::old(count_to(a, n, x)))
{
  *b = 5;
}
// CHECK-DAG: Verified: set_other_rec [backend=z3]

// A write inside the cells may change it.
void set_inside(int *a, int n, int x)
  cv::pre(valid(a, n) && n >= 1 && n <= 100)
  cv::modifies(a[0])
  cv::post(count_to(a, n, x) == cv::old(count_to(a, n, x)))
{
  a[0] = x == 0 ? 1 : 0;
}
// CHECK-DAG: error: verification failed: set_inside [{{.*}}::postcondition@[[@LINE-4]]:30]
