// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s
// RUN: not %cpp-verify --backend=bmc %s -- 2>&1 | FileCheck %s --check-prefix=BMC
// RUN: not %cpp-verify %S/Inputs/clause_proof_rejected.cpp -- 2>&1 \
// RUN:   | FileCheck %s --check-prefix=REJECT
// RUN: not %cpp-verify %S/Inputs/clause_proof_assigns.cpp -- 2>&1 \
// RUN:   | FileCheck %s --check-prefix=ASSIGNS
//
// A spec's post, decreases, and reads clauses take a proof block,
// clause(...) by { ... }: ghost code run in the clause's check after its
// assumptions and before its obligations, where the solver needs a step it
// cannot find, such as a lemma at a chosen argument.

#include <cppverify.h>

cppverify::spec int mul(int a, int b) cppverify::decreases(b) { return b <= 0 ? 0 : mul(a, b - 1) + a; }

cppverify::proof void mul_is(int a, int b)
  cppverify::post(b < 0 || mul(a, b) == a * b)
  cppverify::decreases(b)
{
  if (b > 0)
    mul_is(a, b - 1);
}

// Commutativity needs the lemma at both orders.
cppverify::spec int area(int a, int b)
  cppverify::post(a < 0 || b < 0 || cppverify::result == mul(b, a)) by { mul_is(a, b); mul_is(b, a); }
{
  return mul(a, b);
}
// CHECK-DAG: Verified: spec post: area

cppverify::spec int area_unhelped(int a, int b)
  cppverify::post(a < 0 || b < 0 || cppverify::result == mul(b, a))
{
  return mul(a, b);
}
// CHECK-DAG: Unresolved: spec post unresolved: area_unhelped

// Termination by a measure that the lemma explains.
cppverify::spec int zig(int a, int b)
  cppverify::decreases(mul(a, b)) by { if (a > 0 && b > 0) { mul_is(a, b); mul_is(b - 1, a); } }
{
  return a <= 0 || b <= 0 ? 0 : 1 + zig(b - 1, a);
}
// CHECK-DAG: Verified: spec decreases: zig

cppverify::spec int zig_unhelped(int a, int b)
  cppverify::decreases(mul(a, b))
{
  return a <= 0 || b <= 0 ? 0 : 1 + zig_unhelped(b - 1, a);
}
// CHECK-DAG: Unresolved: spec decreases unresolved: zig_unhelped

// In a post block, result is the value the body returns.
cppverify::spec int twice(int n) cppverify::post(cppverify::result == n + n) by { cppverify::check(cppverify::result - n == n); }
{
  return 2 * n;
}
// CHECK-DAG: Verified: spec post: twice

// An application of the spec in a block assumes its postcondition where
// the measure is lower: the induction hypothesis, at an argument the block
// names.
cppverify::spec int tri(int n)
  cppverify::decreases(n)
  cppverify::post(cppverify::result >= 0) by { if (n > 0) cppverify::check(tri(n - 1) >= 0); }
{
  return n <= 0 ? 0 : tri(n - 1) + n;
}
// CHECK-DAG: Verified: spec decreases and post: tri

// Not above it.
cppverify::spec int up(int n)
  cppverify::decreases(n)
  cppverify::post(cppverify::result >= 0) by { cppverify::check(up(n + 1) >= 0); }
{
  return n <= 0 ? 0 : up(n - 1) + 1;
}
// CHECK-DAG: Unresolved: spec decreases and post unresolved: up

// The block of an inductive predicate's postcondition is the induction
// step: here the premise doubling(mul(a, 2), b) needs mul(a, 2) == 2 * a.
cppverify::spec bool doubling(int a, int b)
  cppverify::inductive
  cppverify::post(!cppverify::result || a <= 0 || a <= b) by { mul_is(a, 2); }
{
  return a == b || (a > 0 && doubling(mul(a, 2), b));
}
// CHECK-DAG: Verified: inductive predicate: doubling
// CHECK-DAG: Verified: spec post: doubling

// A reads check whose index needs the lemma.
cppverify::spec int at(const int *p, int n, int i)
  cppverify::reads(p, n) by { if (0 <= i) mul_is(1, i); }
{
  return 0 <= i && i < n ? p[mul(1, i)] : 0;
}
// CHECK-DAG: Verified: spec reads: at

cppverify::spec int at_unhelped(const int *p, int n, int i)
  cppverify::reads(p, n)
{
  return 0 <= i && i < n ? p[mul(1, i)] : 0;
}
// CHECK-DAG: Unresolved: spec reads unresolved: at_unhelped

// A block cannot use a lemma whose own proof assumes the property: the two
// proofs would rest on each other, and without a shared measure they are no
// induction (suite/proof_clusters.cpp has the measured kind).
cppverify::spec int f(int n);
cppverify::proof void f_lie(int n) cppverify::post(f(n) > 100) {}
cppverify::spec int f(int n)
  cppverify::decreases(n)
  cppverify::post(cppverify::result > 100) by { if (n > 0) f_lie(n - 1); }
{
  return n <= 0 ? 101 : f(n - 1);
}
// CHECK-DAG: Unresolved: f_lie [backend=z3] [reason=proof.cycle]
// CHECK-DAG: Unresolved: spec decreases and post: f [reason=proof.cycle] (relies on the contract of f_lie, whose proof rests in turn on this one; {{.*}}decreases clauses of one length
// BMC-DAG: Unresolved: f_lie [backend=bmc, bound=0] [reason=proof.cycle]
// BMC-DAG: Unresolved: spec decreases and post: f [reason=proof.cycle]

// A lemma's precondition is checked in the block like anywhere else.
cppverify::spec bool bad(int n);
cppverify::proof void lie(int n) cppverify::pre(bad(n)) cppverify::post(false) {}
cppverify::spec bool bad(int n) cppverify::inductive cppverify::post(!cppverify::result || false) by { lie(n); } {
  return n == 0;
}
// CHECK-DAG: error: spec post by induction failed: bad [backend=z3] [reason=counterexample]

// REJECT: clause_proof_rejected.cpp:3:60: error: a proof block follows only a post, decreases, or reads clause of a spec function
// REJECT: clause_proof_rejected.cpp:5:62: error: a proof block follows only a post, decreases, or reads clause of a spec function
// REJECT: clause_proof_rejected.cpp:9:77: error: a proof block belongs to the definition of the function, not to a declaration

// A block is ghost code.
// ASSIGNS-DAG: error: assigns: ghost code cannot modify executable state
// ASSIGNS-DAG: error: returns: ghost code cannot alter executable control flow
// ASSIGNS-DAG: error: stores: ghost code cannot modify executable state
