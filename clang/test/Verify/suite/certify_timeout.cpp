// RUN: not %cpp-verify --certify-timeout=200 %s -- 2>&1 | FileCheck %s
// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s --check-prefix=DEFAULT
//
// Checking one counterexample against the true definitions may take
// --certify-timeout milliseconds (by default half the query timeout), so
// that one model whose check is slow leaves the rest of the query's time to
// the others. The reason says which limit was reached.

#include <cppverify.h>

// The value of leaves(17, 1) takes 2^17 applications to compute: the check
// that needs it is the slow one.
cppverify::spec int leaves(int n, int k)
  cppverify::decreases(n)
{
  return n <= 0 ? k % 2 : leaves(n - 1, 2 * k) + leaves(n - 1, 2 * k + 1);
}

cppverify::proof void no_odd_leaf() cppverify::post(leaves(17, 1) == 0) {}
// CHECK: Unresolved: no_odd_leaf {{.*}}[reason=spec.fuel] {{.*}}checking it needs leaves(17, 1) (the time one counterexample check may take (200 ms, --certify-timeout) was spent while evaluating leaves)
// DEFAULT: error: verification failed: no_odd_leaf [postcondition] [backend=z3] [reason=counterexample]

// odd(4) is false, and its derivations never end: the search of derivation
// heights tries doubling heights, which takes far less than this time limit.
cppverify::spec bool odd(int n) cppverify::inductive { return n == 1 || odd(n - 2); }

cppverify::proof void four_is_odd() cppverify::post(odd(4)) {}
// CHECK: four_is_odd {{.*}}whether odd(4) holds: no derivation was found among the heights tried
// DEFAULT: four_is_odd {{.*}}whether odd(4) holds: no derivation was found among the heights tried
