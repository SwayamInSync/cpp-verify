// RUN: not %cpp-verify --jobs=1 %s -- -std=c++20 2>&1 | FileCheck %s
//
// An expression that evaluates nothing at run time (noexcept, a
// requires-expression, a concept, a type trait, offsetof, __builtin_LINE) is
// the value Clang computes for it. Every correct function has a wrong twin.

#include <cstddef>

namespace cv = cppverify;

struct Pair {
  int first;
  int second;
};

template <typename T>
concept Small = sizeof(T) <= 4;

int facts(int x)
  cv::post(cv::result == 6)
{
  return noexcept(x + 1) + requires { x + 1; } + Small<int> +
         __is_same(int, int) + (offsetof(Pair, second) == 4) +
         (__builtin_LINE() == __LINE__);
}
// CHECK-DAG: Verified: facts [backend=z3]

int facts_wrong(int x)
  cv::post(cv::result == 6)
{
  return noexcept(x + 1) + requires { x + 1; } + Small<long long> +
         __is_same(int, long) + (offsetof(Pair, second) == 0) +
         (__builtin_LINE() == __LINE__ + 1);
}
// CHECK-DAG: error: verification failed: facts_wrong [{{.*}}::postcondition@{{.*}}result [ssa=__result_1] [type=i32] = 2{{.*}}[reason=counterexample]
