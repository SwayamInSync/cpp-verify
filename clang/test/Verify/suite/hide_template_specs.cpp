// RUN: not %cpp-verify --jobs=1 %s -- 2>&1 | FileCheck %s
// RUN: not %cpp-verify --jobs=1 %s -- -DUNNAMED 2>&1 | FileCheck %s --check-prefix=UNNAMED
//
// hide, reveal, and reveal_with_fuel name one specialization of a spec
// template, as at<4> does.

namespace cv = cppverify;

template <int K> cv::spec int scaled(int x) { return K * x; }

template <int K> cv::spec int steps(int n)
  cv::decreases(n)
{
  return n <= 0 ? 0 : K + steps<K>(n - 1);
}

int shown(int x)
  cv::pre(0 <= x && x <= 100)
  cv::post(cv::result == scaled<3>(x))
{
  return 3 * x;
}
// CHECK-DAG: Verified: shown [backend=z3]

// Hidden, the specialization's definition does not reach the proof.
int hidden(int x)
  cv::pre(0 <= x && x <= 100)
  cv::post(cv::result == scaled<3>(x))
{
  cv::hide(scaled<3>);
  return 3 * x;
}
// CHECK-DAG: Unresolved: hidden [backend=z3] [reason=spec.hidden] ({{.*}}the proof needs the definition of scaled<3>, which is hidden from the solver

// Fuel unfolds a recursive specialization as deep as asked.
int fueled()
  cv::post(cv::result == steps<2>(3))
{
  cv::ghost { cv::reveal_with_fuel(steps<2>, 4); }
  return 6;
}
// CHECK-DAG: Verified: fueled [backend=z3]

#ifdef UNNAMED
// The template's name names no one specialization.
int unnamed()
  cv::post(cv::result == 0)
{
  cv::hide(scaled);
  return 0;
}
// UNNAMED: hide_template_specs.cpp:[[@LINE-3]]:12: error: reference to overloaded function could not be resolved; did you mean to call it?
#endif
