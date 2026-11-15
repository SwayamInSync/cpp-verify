// RUN: not %cpp-verify --jobs=1 %s -- -nostdinc++ -isystem %S/Inputs/libcxx_abs > %t 2>&1
// RUN: FileCheck %s < %t
// RUN: not %cpp-verify --jobs=1 %s -- -nostdinc++ -isystem %S/Inputs/ucrt_abs > %t.ucrt 2>&1
// RUN: FileCheck %s < %t.ucrt
//
// std::abs of an integer is its definition wherever the library declares it
// within std: libc++ defines it in std::__math, and the Windows C runtime in
// the global namespace, with a const parameter. An abs in a namespace of the
// user's own is a function like any other.

#include <cppverify.h>
#include <cstdlib>

namespace cv = cppverify;

int magnitude(int x)
  cv::pre(x > -2147483647 - 1)
  cv::post(cv::result >= 0 && (cv::result == x || cv::result == -x))
{
  return std::abs(x);
}
// CHECK-DAG: Verified: magnitude [backend=z3]

long distance(long a, long b)
  cv::pre(-1000000 <= a && a <= 1000000 && -1000000 <= b && b <= 1000000)
  cv::post(cv::result == (a < b ? b - a : a - b))
{
  return std::abs(a - b);
}
// CHECK-DAG: Verified: distance [backend=z3]

long long wide(long long x)
  cv::pre(x > -1000 && x < 1000)
  cv::post(cv::result >= 0)
{
  return std::abs(x);
}
// CHECK-DAG: Verified: wide [backend=z3]

// Undefined at the minimum, as the C library's abs is.
int any_magnitude(int x)
  cv::post(cv::result >= 0)
{
  return std::abs(x);
}
// CHECK-DAG: library_abs_nested_namespace.cpp:[[@LINE-2]]:10: error: verification failed: any_magnitude [overflow]

namespace mine {
namespace math {
[[cppverify::trusted]] int abs(int x)
  cv::post(cv::result == 7);
} // namespace math
} // namespace mine

int own(int x)
  cv::post(cv::result == 7)
{
  return mine::math::abs(x);
}
// CHECK-DAG: Verified: own [backend=z3] [trusts=abs]
