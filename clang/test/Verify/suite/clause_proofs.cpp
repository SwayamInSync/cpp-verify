// RUN: not %cpp-verify %s 2>&1 | FileCheck %s
// RUN: not %cpp-verify --backend=bmc %s 2>&1 | FileCheck %s --check-prefix=BMC
// RUN: not %cpp-verify %S/Inputs/clause_proof_rejected.cpp 2>&1 \
// RUN:   | FileCheck %s --check-prefix=REJECT
// RUN: not %cpp-verify %S/Inputs/clause_proof_assigns.cpp 2>&1 \
// RUN:   | FileCheck %s --check-prefix=ASSIGNS
//
// A spec's post, decreases, and reads clauses take a proof block,
// clause(...) by { ... }: ghost code run in the clause's check after its
// assumptions and before its obligations, where the solver needs a step it
// cannot find, such as a lemma at a chosen argument.

#include <cppverify.h>

spec int mul(int a, int b) decreases(b) { return b <= 0 ? 0 : mul(a, b - 1) + a; }

proof void mul_is(int a, int b)
  post(b < 0 || mul(a, b) == a * b)
  decreases(b)
{
  if (b > 0)
    mul_is(a, b - 1);
}

// Commutativity needs the lemma at both orders.
spec int area(int a, int b)
  post(a < 0 || b < 0 || result == mul(b, a)) by { mul_is(a, b); mul_is(b, a); }
{
  return mul(a, b);
}
// CHECK-DAG: Verified: spec post: area

spec int area_unhelped(int a, int b)
  post(a < 0 || b < 0 || result == mul(b, a))
{
  return mul(a, b);
}
// CHECK-DAG: Unresolved: spec post unresolved: area_unhelped

// Termination by a measure that the lemma explains.
spec int zig(int a, int b)
  decreases(mul(a, b)) by { if (a > 0 && b > 0) { mul_is(a, b); mul_is(b - 1, a); } }
{
  return a <= 0 || b <= 0 ? 0 : 1 + zig(b - 1, a);
}
// CHECK-DAG: Verified: spec decreases: zig

spec int zig_unhelped(int a, int b)
  decreases(mul(a, b))
{
  return a <= 0 || b <= 0 ? 0 : 1 + zig_unhelped(b - 1, a);
}
// CHECK-DAG: Unresolved: spec decreases unresolved: zig_unhelped

// In a post block, result is the value the body returns.
spec int twice(int n) post(result == n + n) by { contract_assert(result - n == n); }
{
  return 2 * n;
}
// CHECK-DAG: Verified: spec post: twice

// An application of the spec in a block assumes its postcondition where
// the measure is lower: the induction hypothesis, at an argument the block
// names.
spec int tri(int n)
  decreases(n)
  post(result >= 0) by { if (n > 0) contract_assert(tri(n - 1) >= 0); }
{
  return n <= 0 ? 0 : tri(n - 1) + n;
}
// CHECK-DAG: Verified: spec decreases and post: tri

// Not above it.
spec int up(int n)
  decreases(n)
  post(result >= 0) by { contract_assert(up(n + 1) >= 0); }
{
  return n <= 0 ? 0 : up(n - 1) + 1;
}
// CHECK-DAG: Unresolved: spec decreases and post unresolved: up

// The block of an inductive predicate's postcondition is the induction
// step: here the premise doubling(mul(a, 2), b) needs mul(a, 2) == 2 * a.
spec bool doubling(int a, int b)
  inductive
  post(!result || a <= 0 || a <= b) by { mul_is(a, 2); }
{
  return a == b || (a > 0 && doubling(mul(a, 2), b));
}
// CHECK-DAG: Verified: inductive predicate: doubling
// CHECK-DAG: Verified: spec post: doubling

// A reads check whose index needs the lemma.
spec int at(const int *p, int n, int i)
  reads(p, n) by { if (0 <= i) mul_is(1, i); }
{
  return 0 <= i && i < n ? p[mul(1, i)] : 0;
}
// CHECK-DAG: Verified: spec reads: at

spec int at_unhelped(const int *p, int n, int i)
  reads(p, n)
{
  return 0 <= i && i < n ? p[mul(1, i)] : 0;
}
// CHECK-DAG: Unresolved: spec reads unresolved: at_unhelped

// A block cannot use a lemma whose own proof assumes the property: the two
// proofs would rest on each other.
spec int f(int n);
proof void f_lie(int n) post(f(n) > 100) {}
spec int f(int n)
  decreases(n)
  post(result > 100) by { if (n > 0) f_lie(n - 1); }
{
  return n <= 0 ? 101 : f(n - 1);
}
// CHECK-DAG: Unresolved: f_lie [backend=z3] [reason=proof.cycle]
// CHECK-DAG: Unresolved: spec decreases and post: f [reason=proof.cycle] (relies on the contract of f_lie, whose proof rests in turn on this one)
// BMC-DAG: Unresolved: f_lie [backend=bmc, bound=0] [reason=proof.cycle]
// BMC-DAG: Unresolved: spec decreases and post: f [reason=proof.cycle]

// A lemma's precondition is checked in the block like anywhere else.
spec bool bad(int n);
proof void lie(int n) pre(bad(n)) post(false) {}
spec bool bad(int n) inductive post(!result || false) by { lie(n); } {
  return n == 0;
}
// CHECK-DAG: error: spec post by induction failed: bad [backend=z3] [reason=counterexample]

// REJECT: clause_proof_rejected.cpp:3:38: error: a proof block follows only a post, decreases, or reads clause of a spec function
// REJECT: clause_proof_rejected.cpp:5:40: error: a proof block follows only a post, decreases, or reads clause of a spec function
// REJECT: clause_proof_rejected.cpp:9:44: error: a proof block belongs to the definition of the function, not to a declaration

// A block is ghost code.
// ASSIGNS-DAG: error: assigns: ghost code cannot modify executable state
// ASSIGNS-DAG: error: returns: ghost code cannot alter executable control flow
// ASSIGNS-DAG: error: stores: ghost code cannot modify executable state
