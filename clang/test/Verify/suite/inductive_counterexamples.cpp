// RUN: not %cpp-verify %s 2>&1 | FileCheck %s
//
// A counterexample may need an inductive predicate to be false somewhere,
// which no derivation height shows. Its check decides that by the least
// fixpoint over the arguments the predicate's derivations reach, when they
// are finitely many, or by a proved postcondition; otherwise the message
// names the application it could not decide.

#include <cppverify.h>
using cppverify::valid;

spec bool edge(int a, int b) { return b == a + 2 || b == 2 * a; }

// Finitely many arguments: every step goes up, and none above b counts.
spec bool climb(int a, int b) inductive {
  return a == b || (a < b && exists(c, edge(a, c) && climb(c, b)));
}

proof void climb_three_four() post(climb(3, 4)) {}
// CHECK-DAG: error: verification failed: climb_three_four {{.*}}[reason=counterexample]

proof void climb_one_four() post(climb(1, 4)) {
  contract_assert(climb(4, 4));
  contract_assert(climb(2, 4));
}
// CHECK-DAG: Verified: climb_one_four

// Defined together, with finitely many arguments.
spec bool ev(int n);
spec bool od(int n) inductive { return n == 1 || (n > 1 && ev(n - 1)); }
spec bool ev(int n) inductive { return n == 0 || (n > 0 && od(n - 1)); }

proof void four_is_odd() post(od(4)) {}
// CHECK-DAG: error: verification failed: four_is_odd {{.*}}[reason=counterexample]

// Reading memory: a cycle that never reaches 5.
spec bool linked(const int *next, int n, int i, int j)
  inductive
  reads(next, n)
{
  return i == j || (0 <= i && i < n && linked(next, n, next[i], j));
}

void around(const int *next)
  pre(valid(next, 2) && next[0] == 1 && next[1] == 0)
{
  contract_assert(linked(next, 2, 0, 5));
}
// CHECK-DAG: error: verification failed: around {{.*}}[reason=counterexample]

// Infinitely many arguments, but a proved postcondition decides it.
spec bool even(int n) inductive post(!result || (n >= 0 && n % 2 == 0)) {
  return n == 0 || even(n - 2);
}

proof void three_is_even() post(even(3)) {}
// CHECK-DAG: error: verification failed: three_is_even {{.*}}[reason=counterexample]

// Neither: the message names the application.
spec bool odd(int n) inductive { return n == 1 || odd(n - 2); }

proof void four_is_odd_too() post(odd(4)) {}
// CHECK-DAG: four_is_odd_too {{.*}}whether odd(4) holds: no derivation was found among the heights tried

// A postcondition that is not established is no evidence: the
// counterexample that used it is not reported as one. ge(-5000) holds, by a
// derivation too tall to find, while the false postcondition says it
// cannot.
spec bool ge(int n);
spec bool ge(int n) inductive post(!result || n > -1000) {
  return n == 20 || ge(n + 1);
}
// CHECK-DAG: error: spec post by induction failed: ge

proof void far() post(ge(-5000)) {}
// CHECK-DAG: Unresolved: verification unresolved: far {{.*}}[reason=spec.post] (its counterexample is checked with the postcondition of ge, which is not established)
