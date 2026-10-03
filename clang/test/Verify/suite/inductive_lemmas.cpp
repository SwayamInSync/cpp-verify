// RUN: not %cpp-verify %s 2>&1 | FileCheck %s
//
// A postcondition of an inductive predicate is a lemma about every
// derivation, proved by induction on derivations. It may mention the
// predicate itself, and the predicates defined with it: there they are seen
// through their proved unfoldings, never through the postcondition being
// proved.

#include <cppverify.h>

spec bool edge(int a, int b) { return b == a + 1 || b == 2 * a; }

// Transitivity: a derivation of reach(a, b) followed by one of reach(b, c).
spec bool reach(int a, int b);
spec bool reach(int a, int b)
  inductive
  post(!result || forall(c, !reach(b, c) || reach(a, c)))
{
  return a == b || exists(c, edge(a, c) && reach(c, b));
}
// CHECK-DAG: Verified: spec post: reach

proof void chain(int a, int b, int c)
  pre(reach(a, b) && reach(b, c))
  post(reach(a, c))
{
}
// CHECK-DAG: Verified: chain

// Case analysis as a postcondition: a premise is a derivation.
spec bool path(int a, int b);
spec bool path(int a, int b)
  inductive
  post(!result || a == b || exists(c, edge(a, c) && path(c, b)))
{
  return a == b || exists(c, edge(a, c) && path(c, b));
}
// CHECK-DAG: Verified: spec post: path

// Predicates defined together: an odd number's successor is even.
spec bool ev(int n);
spec bool od(int n) inductive post(!result || ev(n + 1)) {
  return n == 1 || ev(n - 1);
}
spec bool ev(int n) inductive post(!result || od(n + 1)) {
  return n == 0 || od(n - 1);
}
// CHECK-DAG: Verified: spec post: od
// CHECK-DAG: Verified: spec post: ev

proof void four_after_three() pre(od(3)) post(ev(4)) {}
// CHECK-DAG: Verified: four_after_three

// A postcondition cannot assume itself: bad(0) holds, so !bad(0) fails.
spec bool bad(int n);
spec bool bad(int n) inductive post(!result || !bad(n)) { return n == 0; }
// CHECK-DAG: error: spec post by induction failed: bad [backend=z3] [reason=counterexample] (derivation.height [type=math-i64] = {{[0-9]+}}, n [type=math-i32] = 0)
// CHECK-DAG: Unresolved: spec post: bad [reason=spec.post]

proof void contradiction() post(false) { contract_assert(bad(0)); }
// CHECK-DAG: Unresolved: contradiction {{.*}}[reason=spec.post]
