// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s
// RUN: not %cpp-verify --backend=bmc --unroll=1 %s -- 2>&1 | FileCheck %s
//
// Spec functions may call each other in a cycle when every call within the
// cycle lowers one shared measure. Each function's termination is proved
// with every function of the cycle opaque.

cppverify::spec bool is_odd(int n);

cppverify::spec bool is_even(int n)
  cppverify::decreases(n)
{
  return n <= 0 ? n == 0 : is_odd(n - 1);
}

cppverify::spec bool is_odd(int n)
  cppverify::decreases(n)
{
  return n <= 0 ? false : is_even(n - 1);
}

// pong calls ping at the same argument, so the cycle need not terminate, and
// neither function's termination is established.
cppverify::spec int ping(int n);

cppverify::spec int pong(int n)
  cppverify::decreases(n)
{
  return n <= 0 ? 0 : ping(n) + 1;
}

cppverify::spec int ping(int n)
  cppverify::decreases(n)
{
  return n <= 0 ? 0 : pong(n - 1);
}

void parity()
{
  cppverify::ghost { cppverify::check(is_even(10) && is_odd(7) && !is_even(7)); }
}

void parity_exclusive(int n)
  cppverify::pre(n >= 0 && n <= 50)
{
  cppverify::ghost { cppverify::check(is_even(n) != is_odd(n)); }
}

void parity_wrong(int n)
  cppverify::pre(n >= 0 && n <= 50)
{
  cppverify::ghost { cppverify::check(is_even(n) == is_odd(n)); }
}

// CHECK-DAG: Verified: spec decreases: is_even
// CHECK-DAG: Verified: spec decreases: is_odd
// CHECK-DAG: Unresolved: spec decreases: ping [reason=spec.termination] (relies on the definition of pong, whose termination is not established)
// CHECK-DAG: error: spec decreases failed: pong {{.*}}[reason=counterexample] (n [type=math-i32] = {{[1-9][0-9]*}})
// CHECK-DAG: Verified: parity
// CHECK-DAG: Verified: parity_exclusive
// CHECK-DAG: verification failed: parity_wrong {{.*}}n [ssa=n_0] [type=i32] = {{[0-9]+}}
