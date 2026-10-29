// RUN: %cpp-verify %s -- 2>&1 | FileCheck %s --implicit-check-not=error:
// RUN: %cpp-verify %s -- -DCALL 2>&1 | FileCheck %s --check-prefix=CALL --implicit-check-not=error:
// RUN: %cpp-verify %s -- -DSTATEMENT 2>&1 | FileCheck %s --check-prefix=STATEMENT
//
// A function template without contracts is not verified on its own, and
// stops nothing: verified code that calls it runs its body. One with contract
// statements, as one with contracts, is verified in its specializations, and
// one that nothing instantiates is reported, not verified.

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
// CALL: Verified: uses_twice [backend=z3]
// CALL-NOT: function template verification
// CALL-NOT: twice

#ifdef STATEMENT
template <class T> T checked(T v)
{
  cppverify::check(true);
  return v;
}
#endif
// STATEMENT: warning: checked: function template is not verified: this translation unit instantiates none of its specializations
