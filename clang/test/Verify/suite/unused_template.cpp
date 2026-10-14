// RUN: %cpp-verify %s -- 2>&1 | FileCheck %s --implicit-check-not=error:
// RUN: not %cpp-verify %s -- -DCALL 2>&1 | FileCheck %s --check-prefix=CALL
// RUN: not %cpp-verify %s -- -DSTATEMENT 2>&1 | FileCheck %s --check-prefix=STATEMENT
//
// A function template without contracts is not verified, and stops nothing
// unless verified code calls it: that call is reported. One with contract
// statements is reported, as one with contracts is.

template <class T> T twice(T v) { return v + v; }

int inc(int x)
  cppverify::pre(x < 1000)
  cppverify::post(cppverify::result == x + 1)
{
  return x + 1;
}
// CHECK: Verified: inc [backend=z3]

#ifdef CALL
int uses_twice(int x)
  cppverify::pre(0 <= x && x <= 1000)
  cppverify::post(cppverify::result == 2 * x)
{
  return twice(x);
}
#endif
// CALL: error: uses_twice: call to function without a verification contract: twice
// CALL-NOT: function template verification

#ifdef STATEMENT
template <class T> T checked(T v)
{
  cppverify::check(true);
  return v;
}
#endif
// STATEMENT: error: checked: function template verification is unsupported
