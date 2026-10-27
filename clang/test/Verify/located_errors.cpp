// RUN: not %cpp-verify %s -- -std=c++17 2>&1 | FileCheck %s --strict-whitespace
// RUN: not %cpp-verify --diagnostics-format=json %s -- -std=c++17 2>/dev/null \
// RUN:   | FileCheck %s --check-prefix=JSON
//
// An error about source the verifier cannot represent points at that source,
// with its line and a caret, as a compiler error does, and its JSON record
// carries the range and the verdict of the function it is in.

namespace cv = cppverify;

int pick(int x)
  cv::post(cv::result >= 0)
{
  if (x < 0) throw x; return 0;
}
// CHECK:      {{.*}}located_errors.cpp:[[@LINE-2]]:14: error: pick: throw is unsupported: exceptions are not modeled
// CHECK-NEXT: {{^ +}}[[@LINE-3]] |   if (x < 0) throw x; return 0;
// CHECK-NEXT: {{^ +}}|              ^~~~~~~
// JSON: {"function":"pick","message":"pick: throw is unsupported: exceptions are not modeled","reason":"construct.unsupported","schema":"cppverify.diagnostic/1","severity":"error","source":{"column":14,"end_column":20,"end_line":[[#@LINE-5]],"file":"{{.*}}located_errors.cpp","line":[[#@LINE-5]]},"status":"unresolved"}

struct Shape {
  virtual int get(int x) { cv::check(x >= 0 || x < 0); return x; }
};
// CHECK:      {{.*}}located_errors.cpp:[[@LINE-2]]:15: error: Shape::get: virtual functions are unsupported, since a call may run an override
// CHECK-NEXT: {{^ +}}[[@LINE-3]] |   virtual int get(int x) { cv::check(x >= 0 || x < 0); return x; }
// CHECK-NEXT: {{^ +}}|               ^~~

[[cppverify::trusted]] cv::spec int trusted_spec(int x) { return x; }
// CHECK:      {{.*}}located_errors.cpp:[[@LINE-1]]:37: error: trusted_spec: {{\[\[}}cppverify::trusted]] does not apply to a spec function, whose definition is its meaning
// CHECK-NEXT: {{^ +}}[[@LINE-2]] | {{\[\[}}cppverify::trusted]] cv::spec int trusted_spec(int x) { return x; }
// CHECK-NEXT: {{^ +}}|                                     ^~~~~~~~~~~~

cv::spec int counts(int n)
  cv::inductive
{
  return n;
}
// CHECK:      {{.*}}located_errors.cpp:[[@LINE-4]]:3: error: counts: only a spec function returning bool can be inductive
// CHECK-NEXT: {{^ +}}[[@LINE-5]] |   cv::inductive

// Reported after every function is converted, at the function.
int down(int n)
  cv::post(cv::result == 0)
{
  if (n <= 0)
    return 0;
  int r = down(n - 1);
  return r;
}
// CHECK:      {{.*}}located_errors.cpp:[[@LINE-8]]:5: error: down: recursive executable functions require decreases, or cppverify::decreases(*) to allow divergence
// CHECK-NEXT: {{^ +}}[[@LINE-9]] | int down(int n)
// CHECK-NEXT: {{^ +}}|     ^~~~
// JSON: {"function":"down","message":"down: recursive executable functions require decreases, or cppverify::decreases(*) to allow divergence","reason":"construct.unsupported",{{.*}}"status":"unresolved"}
