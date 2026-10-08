// RUN: %cpp-verify --timeout=30000 %s 2>&1 | FileCheck %s
// RUN: %cpp-verify --timeout=30000 --diagnostics-format=json %s 2>/dev/null \
// RUN:   | FileCheck %s --check-prefix=JSON
//
// A function that is not verified may still call a contracted one, whose
// precondition is then assumed there, not checked (Frama-C reports such a
// property as valid under hypotheses). The callee's verdict says so.

int decrement(int x)
  cppverify::pre(x >= 1)
  cppverify::post(cppverify::result == x - 1)
{
  return x - 1;
}
// CHECK-DAG: Verified: decrement [backend=z3] (its precondition is assumed, not checked, at calls from unverified helper, other)
// JSON-DAG: "function":"decrement"{{.*}}"unverified_callers":["helper","other"]

int helper(int y) { return decrement(y); }
int other(int y) { return decrement(y + 1); }

int verified_caller(int y)
  cppverify::pre(y >= 1)
  cppverify::post(cppverify::result == y - 1)
{
  return decrement(y);
}
// CHECK-DAG: Verified: verified_caller [backend=z3]{{$}}

// No precondition, nothing assumed.
int twice(int x)
  cppverify::pre(true)
  cppverify::post(true)
{
  return x;
}
int calls_twice(int y) { return twice(y); }
// CHECK-DAG: Verified: twice [backend=z3]{{$}}
