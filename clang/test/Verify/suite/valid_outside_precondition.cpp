// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s
// RUN: not %cpp-verify --no-check-ub %s -- 2>&1 | FileCheck %s --check-prefix=NOUB
//
// cppverify::valid(p, n) declares an extent only as a top-level condition of a
// precondition. Anywhere else it would be a spec whose body is true, so a
// claim written with it would hold without meaning anything: it is an error
// for that function, and the other functions are still verified.

namespace cv = cppverify;
using namespace cppverify;

int *in_post(int n)
  cv::pre(n == 4)
  cv::post(valid(cv::result, n))
{
  return nullptr;
}
// CHECK: error: in_post: valid(p, n) declares an extent only as a top-level condition of a cppverify::pre, and has no meaning in a postcondition

int in_invariant(const int *a, int n)
  cv::pre(valid(a, n) && n >= 0)
  cv::post(cv::result == n)
{
  int i = 0;
  while (i < n)
    cv::invariant(0 <= i && i <= n && valid(a, n))
    cv::decreases(n - i)
  {
    i = i + 1;
  }
  return i;
}
// CHECK: error: in_invariant: {{.*}} has no meaning in a loop invariant

int in_check(const int *a, int n)
  cv::pre(valid(a, n) && n > 0)
  cv::post(cv::result == a[0])
{
  cv::check(valid(a, n));
  return a[0];
}
// CHECK: error: in_check: {{.*}} has no meaning in a cppverify::check

int in_ghost(const int *a, int n)
  cv::pre(n > 0)
  cv::post(cv::result == n)
{
  cv::ghost { bool v = valid(a, n); }
  return n;
}
// CHECK: error: in_ghost: {{.*}} has no meaning in ghost code

cv::spec bool in_spec(const int *a, int n) { return valid(a, n) && n > 0; }
// CHECK: error: in_spec: {{.*}} has no meaning in a spec function

int fine(const int *a, int n)
  cv::pre(valid(a, n) && n > 0)
  cv::post(cv::result == a[0])
{
  return a[0];
}
// CHECK: Verified: fine

// Without memory checks every marker folds to true, as the warning says.
// NOUB: warning: contract of in_post uses the valid(p, n) extent marker, but memory checking is disabled (--no-check-ub)
// NOUB: Verified: in_post
// NOUB: warning: contract of in_check uses the valid(p, n) extent marker
