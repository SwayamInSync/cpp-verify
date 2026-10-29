// RUN: %cpp-verify --jobs=1 --timeout=5000 %s -- 2>&1 | FileCheck %s
// RUN: %cpp-verify --lower-only --dump-ir=2 --function=shifted %s -- 2>&1 | FileCheck %s --check-prefix=MIXED
// RUN: %cpp-verify --lower-only --dump-ir=2 --function=both_shifted %s -- 2>&1 | FileCheck %s --check-prefix=SHARED
//
// A callee's quantifier over its parameters' elements is restated over a
// slice actual's base (j := k - c) when every element it reads goes through
// that one slice `base + c`, so that the caller's reads trigger it. When it
// also reads at another offset, no change of variables suits both: an assumed
// postcondition keeps the quantifier and adds its restatement over each
// slice's base, equivalent, and the caller's reads trigger one of them.

namespace cv = cppverify;

[[cppverify::trusted]] void copy(int *d, const int *s, long k)
  cv::pre(cv::valid(d, k) && cv::valid(s, k))
  cv::modifies(d[0 : k])
  cv::post(cv::forall(i, 0, k, d[i] == cv::old(s[i])));

[[cppverify::trusted]] bool all_positive(const int *s, long k)
  cv::pre(cv::valid(s, k))
  cv::post(cv::result == cv::forall(i, 0, k, s[i] > 0));

void shifted(int *a, const int *b, int n)
  cv::pre(cv::valid(a, n) && cv::valid(b, n + 1) && 1 <= n && n <= 1000)
  cv::modifies(a[0 : n])
  cv::post(cv::forall(k, 0, n, a[k] == b[k + 1]))
{
  copy(a, b + 1, n);
}
// CHECK-DAG: Verified: shifted [backend=z3] [trusts=copy]
// MIXED: forall __cppverify_bound_0_i{{$}}
// MIXED: forall __cppverify_bound_0_i_rebased{{$}}

void shifted_target(int *a, const int *b, int n)
  cv::pre(cv::valid(a, n + 1) && cv::valid(b, n) && 1 <= n && n <= 1000)
  cv::modifies(a[0 : n + 1])
  cv::post(cv::forall(k, 1, n + 1, a[k] == b[k - 1]))
{
  copy(a + 1, b, n);
}
// CHECK-DAG: Verified: shifted_target [backend=z3] [trusts=copy]

bool both_shifted(const int *b, int n)
  cv::pre(cv::valid(b, n + 1) && 1 <= n && n <= 1000)
  cv::post(cv::result == cv::forall(k, 1, n + 1, b[k] > 0))
{
  return all_positive(b + 1, n);
}
// CHECK-DAG: Verified: both_shifted [backend=z3] [trusts=all_positive]
// SHARED: _rebased
