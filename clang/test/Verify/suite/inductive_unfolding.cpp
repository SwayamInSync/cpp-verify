// RUN: not %cpp-verify --timeout=10000 %s 2>&1 \
// RUN:   | FileCheck %s --implicit-check-not=invalid-result
//
// How far a proof sees an inductive predicate. Each named application
// unfolds once; an application at constant arguments is decided before
// solving, and its derivation's unfoldings reach the solver;
// reveal_with_fuel(P, n) unfolds n levels; and a verdict that still depends
// on the predicate is retried one level deeper at a time, up to four. Every
// level is a proved unfolding, so false claims still fail.

#include <cppverify.h>
using cppverify::valid;

spec bool edge(int a, int b) { return b == a + 1 || b == 2 * a; }

spec bool reach(int a, int b) inductive {
  return a == b || exists(c, edge(a, c) && reach(c, b));
}

// 1 -> 2 -> 4, found by the counterexample check, given as unfoldings.
proof void constant() post(reach(1, 4)) {}
// CHECK-DAG: Verified: constant

// Four levels below the named application, found by deepening.
proof void deepened(int b) pre(b == 8) post(reach(1, b)) {}
// CHECK-DAG: Verified: deepened

// Six levels: beyond deepening, within the fuel asked for.
proof void fueled(int b) pre(b == 32) post(reach(1, b)) {
  ghost { reveal_with_fuel(reach, 6); }
}
// CHECK-DAG: Verified: fueled

// 1 + 1 = 2 is not 3, but 3 is reached from 1 by 1 -> 2 -> 3.
proof void wrong_target(int b) pre(b == 3) post(!reach(1, b)) {}
// CHECK-DAG: error: verification failed: wrong_target {{.*}}[reason=counterexample]

// Unfolding the applications inside an unfolding nests the body in itself,
// so its binders are renamed apart. Captured, the second level read
// rise(c, b) == (c == b || rise(0, b)), and rise(0, 3) proved rise(5, 3).
spec bool rise(int a, int b)
  inductive
  post(!result || a < 0 || a <= b)
{
  return a == b || exists(c, edge(a, c) && rise(c, b));
}

proof void renamed_apart(int b) pre(b == 3 && rise(0, b)) post(rise(5, b)) {
  ghost { reveal_with_fuel(rise, 2); }
}
// CHECK-DAG: error: verification failed: renamed_apart {{.*}}[reason=counterexample]

// The same for a recursive spec's fuel levels: captured, the inner
// k + 1 == n read k + 1 == k, and g(2) was false.
spec bool g(int n) decreases(n) {
  return n <= 0 ? true : exists(k, 0, n, k + 1 == n && g(k));
}

proof void fuel_levels_apart() post(!g(2)) {
  ghost { reveal_with_fuel(g, 3); }
}
// CHECK-DAG: error: verification failed: fuel_levels_apart {{.*}}[reason=counterexample]

proof void fuel_levels() post(g(2)) {
  ghost { reveal_with_fuel(g, 3); }
}
// CHECK-DAG: Verified: fuel_levels

spec bool linked(const int *next, int n, int i, int j)
  inductive
  reads(next, n)
{
  return i == j || (0 <= i && i < n && linked(next, n, next[i], j));
}

// The application after the store is unfolded in the memory it reads.
void relink(int *next)
  pre(valid(next, 2) && next[0] == 0 && next[1] == 0)
  modifies(next[0 : 2])
{
  next[0] = 1;
  contract_assert(linked(next, 2, 0, 1));
}
// CHECK-DAG: Verified: relink

void relink_wrong(int *next)
  pre(valid(next, 2) && next[0] == 0 && next[1] == 0)
  modifies(next[0 : 2])
{
  next[0] = 1;
  contract_assert(!linked(next, 2, 0, 1));
}
// CHECK-DAG: error: verification failed: relink_wrong {{.*}}[reason=counterexample]

// Index 0 points to itself forever: linked(next, 2, 0, 1) is false, which
// no unfolding shows. The reason names the application and what supplies
// it, never a solver fault.
void cycle(int *next)
  pre(valid(next, 2) && next[0] == 0 && next[1] == 0)
{
  contract_assert(!linked(next, 2, 0, 1));
}
// CHECK-DAG: Unresolved: cycle {{.*}}[reason=spec.fuel] {{.*}}every counterexample found needs linked({{.*}}0, 1) to hold, but no derivation shows it

// A false postcondition of a predicate fails with a derivation height.
spec bool path(int a, int b);
spec bool path(int a, int b)
  inductive
  post(!result || !path(a, b))
{
  return a == b || exists(c, edge(a, c) && path(c, b));
}
// CHECK-DAG: error: spec post by induction failed: path {{.*}}[reason=counterexample] ({{.*}}derivation.height [type=math-i64] = 1)
