// RUN: not %cpp-verify %s 2>&1 | FileCheck %s
// RUN: not %cpp-verify --backend=bmc --unroll=1 %s 2>&1 | FileCheck %s
// RUN: not %cpp-verify --diagnostics-format=json %s 2>&1 \
// RUN:   | FileCheck %s --check-prefix=JSON
//
// A spec's definition is an axiom only once the spec terminates, so the
// definition is never available to its own termination proof: every
// recursive call must decrease the measure whatever the other calls return.

// Only the component that decides a lexicographic decrease is bounded below,
// so the inner call's value need not be known.
cppverify::spec int ack(int m, int n)
  cppverify::decreases(m, n)
{
  return m <= 0 ? n + 1
       : n <= 0 ? ack(m - 1, 1)
       : ack(m - 1, ack(m, n - 1));
}

void ack_values()
{
  cppverify::ghost { cppverify::check(ack(1, 1) == 3 && ack(2, 2) == 7); }
}

// f(1) calls f(1): the argument chosen for the earlier call is short-circuited
// at n == 1, so its own equation there would read f(1) == !f(1). Using it
// would make the termination check vacuous; without it the call at n == 1 is
// a counterexample.
cppverify::spec bool diverges_at_one(int n)
  cppverify::decreases(n)
{
  return n <= 0 ? true
       : ((n > 1 && diverges_at_one(n > 1 ? n - 1 : n)) ||
          !diverges_at_one(n));
}

// A proof that uses a spec whose termination is not established proves
// nothing: here the spec's equation at 1 would read f(1) == !f(1).
void uses_divergent()
{
  cppverify::ghost { cppverify::check(diverges_at_one(1) == !diverges_at_one(1)); }
}

// Terminates, but only because nested(n) == n, which is not known while its
// termination is being proved.
cppverify::spec int nested(int n)
  cppverify::decreases(n)
{
  return n <= 0 ? 0 : 1 + nested(nested(n - 1));
}

cppverify::spec int second_unbounded(int m, int n)
  cppverify::decreases(m, n)
{
  return m <= 0 ? 0 : second_unbounded(m, n - 1);
}

cppverify::spec int first_unbounded(int m, int n)
  cppverify::decreases(m, n)
{
  return n <= 0 ? 0 : first_unbounded(m - 1, n);
}

// A call under a quantifier happens at every value in its range.
cppverify::spec bool all_below(int n)
  cppverify::decreases(n)
{
  return n <= 0 || cppverify::forall(i, 0, n, all_below(i));
}

cppverify::spec bool reaches_itself(int n)
  cppverify::decreases(n)
{
  return n < 0 || cppverify::forall(i, 0, n + 1, !reaches_itself(i));
}

void all_below_small(int n)
  cppverify::pre(n >= 0 && n <= 5)
{
  cppverify::ghost { cppverify::check(all_below(n)); }
}

// CHECK-DAG: Verified: spec decreases: ack
// CHECK-DAG: Verified: ack_values
// CHECK-DAG: error: spec decreases failed: diverges_at_one {{.*}}[reason=counterexample] (n [type=math-i32] = 1)
// CHECK-DAG: Unresolved: uses_divergent [backend={{z3|bmc, bound=[0-9]+}}]{{( \[vacuous\])?}} [reason=spec.termination] (relies on the definition of diverges_at_one, whose termination is not established)
// CHECK-DAG: Unresolved: spec decreases unresolved: nested {{.*}}a definition cannot be used to prove its own termination
// CHECK-DAG: error: spec decreases failed: second_unbounded {{.*}}[reason=counterexample] (m [type=math-i32] = {{[1-9][0-9]*}}, n [type=math-i32] = {{-?[0-9]+}})
// CHECK-DAG: error: spec decreases failed: first_unbounded {{.*}}[reason=counterexample] (m [type=math-i32] = {{-?[0-9]+}}, n [type=math-i32] = {{[1-9][0-9]*}})

// CHECK-DAG: Verified: spec decreases: all_below
// CHECK-DAG: Verified: all_below_small
// CHECK-DAG: error: spec decreases failed: reaches_itself {{.*}}[reason=counterexample] (n [type=math-i32] = {{[0-9]+}})

// JSON-DAG: "function":"diverges_at_one"{{.*}}"status":"failed"
// JSON-DAG: "function":"ack"{{.*}}"status":"verified"
// JSON-DAG: "function":"uses_divergent"{{.*}}"reason":"spec.termination"{{.*}}"status":"unresolved"
