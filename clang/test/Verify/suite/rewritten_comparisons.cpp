// RUN: not %cpp-verify %s -- -std=c++20 2>&1 | FileCheck %s --implicit-check-not=error:
//
// From C++20 a comparison may be rewritten in terms of another operator:
// a != b through operator==, and 5 == r reversed into r == 5. Each is the
// call it is rewritten to, checked against that operator's contract.

namespace cv = cppverify;

struct Q {
  int v;
  bool operator==(const Q &o) const
    cv::post(cv::result == (v == o.v))
  {
    return v == o.v;
  }
};
// CHECK-DAG: Verified: Q::operator==

bool differ(const Q &a, const Q &b)
  cv::post(cv::result == (a.v != b.v))
{
  return a != b;
}
// CHECK-DAG: Verified: differ

// The rewritten form is negated: it does not mean equality.
bool differ_wrong(const Q &a, const Q &b)
  cv::post(cv::result == (a.v == b.v))
{
  return a != b;
}
// CHECK-DAG: error: verification failed: differ_wrong [postcondition]

struct R {
  int v;
  bool operator==(int o) const
    cv::post(cv::result == (v == o))
  {
    return v == o;
  }
};
// CHECK-DAG: Verified: R::operator==

// Reversed: 5 == r is r.operator==(5).
bool five(const R &r)
  cv::post(cv::result == (r.v == 5))
{
  return 5 == r;
}
// CHECK-DAG: Verified: five

bool not_five(const R &r)
  cv::post(cv::result == (r.v != 5))
{
  return 5 != r;
}
// CHECK-DAG: Verified: not_five

bool not_five_wrong(const R &r)
  cv::post(cv::result == (r.v == 5))
{
  return 5 != r;
}
// CHECK-DAG: error: verification failed: not_five_wrong [postcondition]

// In a condition, as an operand of another operator.
int count_equal(const Q &a, const Q &b, const R &r)
  cv::post(cv::result == (a.v == b.v ? 1 : 0) + (r.v == 5 ? 1 : 0))
{
  int n = 0;
  if (!(a != b))
    n = n + 1;
  return n + (5 == r ? 1 : 0);
}
// CHECK-DAG: Verified: count_equal
