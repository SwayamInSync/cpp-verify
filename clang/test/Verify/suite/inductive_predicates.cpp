// RUN: not %cpp-verify %s 2>&1 | FileCheck %s
// RUN: not %cpp-verify %S/Inputs/inductive_rejected.cpp 2>&1 \
// RUN:   | FileCheck %s --check-prefix=REJECT
// RUN: not %clang -std=c++17 -fverify-contracts -fsyntax-only \
// RUN:   %S/Inputs/inductive_not_spec.cpp 2>&1 | FileCheck %s --check-prefix=NOTSPEC
//
// An inductive predicate is the least one its body defines: true exactly
// where a finite derivation shows it. Proofs see its body at each
// application, and a postcondition !result || Q holds by induction on the
// derivations.

#include <cppverify.h>

// No measure exists: even(-2) would need even(-4), and so on forever, which
// no derivation provides, so it is false.
spec bool even(int n)
  inductive
  post(!result || (n >= 0 && n % 2 == 0))
{
  return n == 0 || even(n - 2);
}
// CHECK-DAG: Verified: spec post: even

// Each named application unfolds once.
proof void four_is_even()
  post(even(4))
{
  contract_assert(even(0));
  contract_assert(even(2));
}
// CHECK-DAG: Verified: four_is_even

// From the postcondition: every derivation is of a nonnegative even number.
proof void even_nonnegative(int n)
  pre(even(n))
  post(n >= 0)
{
}
// CHECK-DAG: Verified: even_nonnegative

// Inversion: an even number other than 0 came from n - 2.
proof void even_step_back(int n)
  pre(even(n) && n != 0)
  post(even(n - 2))
{
}
// CHECK-DAG: Verified: even_step_back

spec bool edge(int a, int b) { return b == a + 1 || b == 2 * a; }

// Reachability: the least relation closed under edges.
spec bool reach(int a, int b)
  inductive
  post(!result || a < 0 || a <= b)
{
  return a == b || exists(c, edge(a, c) && reach(c, b));
}
// CHECK-DAG: Verified: spec post: reach

proof void one_reaches_four()
  post(reach(1, 4))
{
  contract_assert(reach(4, 4));
  contract_assert(reach(2, 4));
}
// CHECK-DAG: Verified: one_reaches_four

proof void reach_grows(int a, int b)
  pre(a >= 0 && reach(a, b))
  post(a <= b)
{
}
// CHECK-DAG: Verified: reach_grows

// A predicate with no measure at all.
spec bool reaches_one(int n)
  inductive
{
  return n == 1 || (n > 1 && reaches_one(n % 2 == 0 ? n / 2 : 3 * n + 1));
}
// CHECK-DAG: Verified: inductive predicate: reaches_one

proof void six_reaches_one()
  post(reaches_one(6))
{
  contract_assert(reaches_one(1));
  contract_assert(reaches_one(2));
  contract_assert(reaches_one(4));
  contract_assert(reaches_one(8));
  contract_assert(reaches_one(16));
  contract_assert(reaches_one(5));
  contract_assert(reaches_one(10));
  contract_assert(reaches_one(3));
}
// CHECK-DAG: Verified: six_reaches_one

// A false claim: its counterexample is certified by a derivation of even(4).
proof void four_is_odd()
  post(!even(4))
{
  contract_assert(even(0));
  contract_assert(even(2));
}
// CHECK-DAG: error: verification failed: four_is_odd {{.*}}[reason=counterexample]

// A postcondition that is not true of every derivation.
spec bool odd(int n)
  inductive
  post(!result || n % 4 == 1)
{
  return n == 1 || odd(n - 2);
}
// CHECK-DAG: error: spec post by induction failed: odd [backend=z3] [reason=counterexample] (derivation.height [type=math-i64] = {{[0-9]+}}, n [type=math-i32] = {{[0-9]+}})
// CHECK-DAG: Unresolved: spec post: odd [reason=spec.post] (relies on the postcondition of odd.step, which is not established)

// REJECT-DAG: error: negated: negated occurs in its body under negation; an inductive predicate occurs in its body only positively
// REJECT-DAG: error: compared: compared occurs in its body in a comparison or arithmetic
// REJECT-DAG: error: everywhere: everywhere occurs in its body under a forall without bounds
// REJECT-DAG: error: chosen: chosen occurs in its body in a condition
// REJECT-DAG: error: counted: only a spec function returning bool can be inductive
// REJECT-DAG: error: measured: an inductive predicate holds by its derivations, so it takes no decreases
// REJECT-DAG: error: exact: a postcondition of an inductive predicate states what holds where it is true, as !result || Q
// REJECT-DAG: error: through: an inductive predicate applies itself only in its body or through inductive predicates, not through another spec

// NOTSPEC: error: only a spec function can be inductive
