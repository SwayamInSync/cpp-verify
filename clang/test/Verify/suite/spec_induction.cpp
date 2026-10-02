// RUN: not %cpp-verify %s 2>&1 | FileCheck %s
// RUN: not %cpp-verify --backend=bmc --unroll=1 %s 2>&1 | FileCheck %s
//
// When no finite unfolding settles a goal about a recursive spec, the
// verifier proves it by strong induction on an integer variable: the goal
// holds if it holds whenever it holds at every smaller nonnegative value of
// that variable, all else fixed. A least counterexample would satisfy that
// hypothesis, so nothing false is proved; below zero the hypothesis is empty.

spec int sum(int n) decreases(n) { return n <= 0 ? 0 : n + sum(n - 1); }
spec int pow2(int n) decreases(n) { return n <= 0 ? 1 : 2 * pow2(n - 1); }

// The lemma needs no body.
proof void sum_closed(int n)
  pre(n >= 0 && n <= 40000)
  post(2 * sum(n) == n * (n + 1))
{
}
// CHECK-DAG: Verified: sum_closed

proof void sum_nonnegative(int n)
  post(sum(n) >= 0)
{
}
// CHECK-DAG: Verified: sum_nonnegative

proof void pow2_positive(int n)
  pre(n >= 0)
  post(pow2(n) >= 1)
{
}
// CHECK-DAG: Verified: pow2_positive

// The result is substituted for its definition before the induction.
int twice_sum(int n)
  pre(n >= 0 && n <= 40000)
  post(result == 2 * sum(n))
{
  return n * (n + 1);
}
// CHECK-DAG: Verified: twice_sum

// A false claim with true base cases still fails, at a counterexample
// checked against the definition.
proof void sum_wrong_once(int n)
  pre(n >= 0 && n <= 300)
  post(2 * sum(n) == n * (n + 1) + (n == 200 ? 1 : 0))
{
}
// CHECK-DAG: error: verification failed: sum_wrong_once {{.*}}(counterexample: n [ssa=n_0] [type=i32] = 200)

proof void pow2_bounded(int n)
  pre(n >= 0)
  post(pow2(n) <= 1000000)
{
}
// CHECK-DAG: error: verification failed: pow2_bounded {{.*}}[reason=counterexample]

// The hypothesis is never available at the value itself.
proof void sum_is_seven(int n)
  pre(n >= 0)
  post(sum(n) == 7)
{
}
// CHECK-DAG: error: verification failed: sum_is_seven {{.*}}[reason=counterexample]

// Below zero the hypothesis is empty: a claim that fails for negative n is
// refuted there.
proof void closed_form_everywhere(int n)
  pre(n <= 1000)
  post(2 * sum(n) == n * (n + 1))
{
}
// CHECK-DAG: error: verification failed: closed_form_everywhere {{.*}}(counterexample: n [ssa=n_0] [type=i32] = -{{[0-9]+}})
