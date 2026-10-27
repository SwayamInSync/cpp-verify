// RUN: not %cpp-verify --lower-only %s -- -std=c++20 -fopenmp 2>&1 | FileCheck %s --implicit-check-not=error:
//
// Each construct the verifier does not represent is named as C++ names it, at
// its location, once: a use of a variable whose initializer was rejected
// reports nothing more, and neither does a call that was.

namespace cv = cppverify;

int jump(int x)
  cv::post(true)
{
  if (x)
    goto out;
  x = 1;
out:
  return x;
}
// CHECK: unsupported_constructs.cpp:[[@LINE-5]]:5: error: jump: goto is unsupported
// CHECK: unsupported_constructs.cpp:[[@LINE-4]]:1: error: jump: labels are unsupported

int computed(int x)
  cv::post(true)
{
  void *target = &&done;
  goto *target;
done:
  return x;
}
// CHECK: unsupported_constructs.cpp:[[@LINE-5]]:18: error: computed: the address of a label is unsupported
// CHECK: unsupported_constructs.cpp:[[@LINE-5]]:3: error: computed: a computed goto is unsupported
// CHECK: unsupported_constructs.cpp:[[@LINE-5]]:1: error: computed: labels are unsupported

int raise(int x)
  cv::post(true)
{
  if (x < 0)
    throw x;
  return x > 0 ? x : throw 0;
}
// CHECK: unsupported_constructs.cpp:[[@LINE-3]]:5: error: raise: throw is unsupported: exceptions are not modeled
// CHECK: unsupported_constructs.cpp:[[@LINE-3]]:22: error: raise: throw is unsupported: exceptions are not modeled

int guarded(int x)
  cv::post(true)
{
  try {
    x = 1;
  } catch (...) {
  }
  return x;
}
// CHECK: unsupported_constructs.cpp:[[@LINE-6]]:3: error: guarded: try is unsupported: exceptions are not modeled

int assembly(int x)
  cv::post(true)
{
  asm("nop");
  return x;
}
// CHECK: unsupported_constructs.cpp:[[@LINE-3]]:3: error: assembly: inline assembly is unsupported

int statement_expression(int x)
  cv::post(true)
{
  int y = ({ int z = x; z; });
  return y + 1;
}
// CHECK: unsupported_constructs.cpp:[[@LINE-3]]:11: error: statement_expression: a statement expression is unsupported

int compound(int x)
  cv::post(true)
{
  int y = (int){3};
  return x + y;
}
// CHECK: unsupported_constructs.cpp:[[@LINE-3]]:11: error: compound: a compound literal is unsupported

int closure(int x)
  cv::post(true)
{
  auto twice = [](int y) { return 2 * y; };
  return x;
}
// CHECK: unsupported_constructs.cpp:[[@LINE-3]]:16: error: closure: lambdas are unsupported

int text(int x)
  cv::post(true)
{
  const char *s = "abc";
  return x;
}
// CHECK: unsupported_constructs.cpp:[[@LINE-3]]:19: error: text: a pointer into a string literal is unsupported; read its characters by index

int name(int x)
  cv::post(true)
{
  const char *s = __func__;
  return x;
}
// CHECK: unsupported_constructs.cpp:[[@LINE-3]]:19: error: name: __func__ as a pointer is unsupported

int helper(int x);

int uncontracted(int x)
  cv::post(true)
{
  return helper(x) + 1;
}
// CHECK: unsupported_constructs.cpp:[[@LINE-2]]:10: error: uncontracted: call to function without a verification contract: helper

// A construct without a name of its own is named by Clang's class.
int simd_sum(int x)
  cv::post(true)
{
  int s = 0;
#pragma omp simd
  for (int i = 0; i < 4; i = i + 1)
    s = s + 1;
  return s + x;
}
// CHECK: unsupported_constructs.cpp:[[@LINE-5]]:1: error: simd_sum: this statement is unsupported (OMPSimdDirective)
