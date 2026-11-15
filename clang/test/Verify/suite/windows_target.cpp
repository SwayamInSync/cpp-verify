// RUN: not %cpp-verify --jobs=1 %s -- %windows_target 2>&1 | FileCheck %s --check-prefixes=CHECK,WINDOWS
// RUN: %cpp-verify --jobs=1 %s -- %linux_target 2>&1 | FileCheck %s --check-prefixes=CHECK,LINUX
//
// The verifier models the target. For Windows, long has 32 bits, and a
// template is parsed where it is defined although the compiler would delay
// that there: its contract belongs to its definition.

#include <cppverify.h>

namespace cv = cppverify;

long sum(int a, int b)
  cv::post(cv::result == a + b)
{
  return static_cast<long>(a) + b;
}
// WINDOWS-DAG: windows_target.cpp:[[@LINE-2]]:31: error: verification failed: sum [overflow] [backend=z3] [reason=counterexample]
// LINUX-DAG: Verified: sum [backend=z3]

long long wide(int a, int b)
  cv::post(cv::result == a + b)
{
  return static_cast<long long>(a) + b;
}
// CHECK-DAG: Verified: wide [backend=z3]

template <typename T> T twice(T x)
  cv::pre(x >= 0 && x <= 100)
  cv::post(cv::result == 2 * x)
{
  return x + x;
}
// CHECK-DAG: Verified: twice<int> [backend=z3]

int four_times(int x)
  cv::pre(x >= 0 && x <= 25)
  cv::post(cv::result == 4 * x)
{
  return twice(twice(x));
}
// CHECK-DAG: Verified: four_times [backend=z3]

template <int K> cv::spec int scaled(int x) { return K * x; }

int tripled(int x)
  cv::pre(0 <= x && x <= 100)
  cv::post(cv::result == scaled<3>(x))
{
  return 3 * x;
}
// CHECK-DAG: Verified: tripled [backend=z3]

template <typename T> struct Box {
  T value;
  T get() const
    cv::post(cv::result == value)
  {
    return value;
  }
  template <typename U> U plus(U more) const
    cv::pre(value >= 0 && value <= 100 && more >= 0 && more <= 100)
    cv::post(cv::result == value + more)
  {
    return value + more;
  }
};

int unbox(const Box<int> &box)
  cv::pre(box.value >= 0 && box.value <= 100)
  cv::post(cv::result == box.value + 1)
{
  return box.plus(1) + box.get() - box.get();
}
// CHECK-DAG: Verified: Box<int>::get [backend=z3]
// CHECK-DAG: Verified: Box<int>::plus<int> [backend=z3]
// CHECK-DAG: Verified: unbox [backend=z3]
