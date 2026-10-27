// RUN: not %cpp-verify --timeout=20000 %s -- 2>&1 | FileCheck %s
//
// A call inside a choose is a call of the function the choose is in: it must
// lower the measure for every value the choice may take.

// Every application inside the choose lowers n.
cppverify::spec int depth(int n)
  cppverify::decreases(n)
{
  return n <= 0 ? 0 : cppverify::choose(k, k == depth(n - 1) + 1);
}
// CHECK-DAG: Verified: spec decreases: depth

// The binder ranges over [0, n), below n.
cppverify::spec int below(int n)
  cppverify::decreases(n)
{
  return n <= 0 ? 0 : cppverify::choose(k, 0, n, below(k) == 0);
}
// CHECK-DAG: Verified: spec decreases: below

// The direct call lowers n, the one inside the choose does not.
cppverify::spec int stuck(int n)
  cppverify::decreases(n)
{
  return n <= 0 ? 0 : stuck(n - 1) + cppverify::choose(k, n == 1 ? k == stuck(n) + 1 : k == 0);
}
// CHECK-DAG: error: spec decreases failed: stuck [backend=z3] [reason=counterexample]
// CHECK-DAG: note: counterexample: {{.*}}n = 1{{( ->|,|$)}}

// The same with a postcondition, which is proved with termination.
cppverify::spec int stuck_post(int n)
  cppverify::decreases(n)
  cppverify::post(cppverify::result >= 0)
{
  return n <= 0 ? 0 : cppverify::choose(k, n == 1 ? k == stuck_post(n) + 1 : k == 0);
}
// CHECK-DAG: error: spec decreases and post failed: stuck_post [backend=z3] [reason=counterexample]
// CHECK-DAG: note: counterexample: {{.*}}n = 1{{( ->|,|$)}}

// The axiom of a choose holds where its applications lower the measure,
// which places the choice in [0, n).
cppverify::spec int pick(int n)
  cppverify::decreases(n)
{
  return n <= 0 ? 0 : pick(cppverify::choose(k, 0, n, k == 0 || pick(k) > 3));
}
// CHECK-DAG: Verified: spec decreases: pick

// An unbounded binder can be any value, so the call need not be lower.
cppverify::spec int unbounded(int n)
  cppverify::decreases(n)
{
  return n <= 0 ? 0 : cppverify::choose(k, unbounded(k) == 0);
}
// CHECK-DAG: error: spec decreases failed: unbounded [backend=z3] [reason=counterexample]
// CHECK-DAG: note: counterexample: {{.*}}n = {{[1-9][0-9]*}}{{( ->|,|$)}}

int forty_two(int x)
  cppverify::post(cppverify::result == 42)
{
  cppverify::check(stuck(x) == stuck(x));
  if (x == 1)
    return 0;
  return 42;
}
// CHECK-DAG: Unresolved: forty_two [backend=z3] [reason=spec.termination] (relies on the definition of stuck, whose termination is not established)

// A choose that does not apply its own function is unaffected.
cppverify::spec int half(int n) { return cppverify::choose(k, 2 * k == n); }
cppverify::proof void halves()
  cppverify::post(half(8) == 4)
{
}
// CHECK-DAG: Verified: halves
