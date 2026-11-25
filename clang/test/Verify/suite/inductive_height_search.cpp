// RUN: not %python %S/Inputs/within_seconds.py 120 %cpp-verify %s -- 2>&1 | FileCheck %s
//
// From an argument, this predicate's derivations reach infinitely many
// arguments, so the check of a counterexample decides it by the height of a
// derivation. A derivation of height h is one of every greater height, so
// the heights tried double. reach(1, 100) has a derivation of height 9:
// trying every height in turn found it in 9 s, and a search given a small
// slice of steps, which its two thousand tries shared, did not find it.

namespace cv = cppverify;

cv::spec bool edge(int a, int b) { return b == a + 1 || b == 2 * a; }

cv::spec bool reach(int a, int b)
  cv::inductive
{
  return a == b || cv::exists(c, edge(a, c) && reach(c, b));
}

cv::proof void reached() cv::post(reach(1, 100)) {}
cv::proof void not_reached() cv::post(!reach(1, 100)) {}

// No derivation, at any height: undecided, and said so at once.
cv::proof void backwards() cv::post(reach(100, 1)) {}

// CHECK-DAG: Verified: reached [backend=z3]
// CHECK-DAG: error: verification failed: not_reached [postcondition] [backend=z3] [reason=counterexample]
// CHECK-DAG: Unresolved: backwards {{.*}}[reason=spec.fuel] {{.*}}whether reach(100, 1) holds: no derivation was found among the heights tried
// CHECK: Summary: 2 verified, 1 failed, 1 unresolved
