// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s
// RUN: not %cpp-verify --backend=bmc --unroll=1 %s -- 2>&1 | FileCheck %s
//
// When no finite unfolding settles a goal about a recursive spec, the
// verifier proves it by strong induction on an integer variable: the goal
// holds if it holds whenever it holds at every smaller nonnegative value of
// that variable, all else fixed. A least counterexample would satisfy that
// hypothesis, so nothing false is proved; below zero the hypothesis is empty.

cppverify::spec int sum(int n) cppverify::decreases(n) { return n <= 0 ? 0 : n + sum(n - 1); }
cppverify::spec int pow2(int n) cppverify::decreases(n) { return n <= 0 ? 1 : 2 * pow2(n - 1); }

// The lemma needs no body.
cppverify::proof void sum_closed(int n)
  cppverify::pre(n >= 0 && n <= 40000)
  cppverify::post(2 * sum(n) == n * (n + 1))
{
}
// CHECK-DAG: Verified: sum_closed

cppverify::proof void sum_nonnegative(int n)
  cppverify::post(sum(n) >= 0)
{
}
// CHECK-DAG: Verified: sum_nonnegative

cppverify::proof void pow2_positive(int n)
  cppverify::pre(n >= 0)
  cppverify::post(pow2(n) >= 1)
{
}
// CHECK-DAG: Verified: pow2_positive

// The result is substituted for its definition before the induction.
int twice_sum(int n)
  cppverify::pre(n >= 0 && n <= 40000)
  cppverify::post(cppverify::result == 2 * sum(n))
{
  return n * (n + 1);
}
// CHECK-DAG: Verified: twice_sum

// A false claim with true base cases still fails, at a counterexample
// checked against the definition.
cppverify::proof void sum_wrong_once(int n)
  cppverify::pre(n >= 0 && n <= 300)
  cppverify::post(2 * sum(n) == n * (n + 1) + (n == 200 ? 1 : 0))
{
}
// CHECK-DAG: error: verification failed: sum_wrong_once {{.*}}(counterexample: n [ssa=n_0] [type=i32] = 200)

cppverify::proof void pow2_bounded(int n)
  cppverify::pre(n >= 0)
  cppverify::post(pow2(n) <= 1000000)
{
}
// CHECK-DAG: error: verification failed: pow2_bounded {{.*}}[reason=counterexample]

// The hypothesis is never available at the value itself.
cppverify::proof void sum_is_seven(int n)
  cppverify::pre(n >= 0)
  cppverify::post(sum(n) == 7)
{
}
// CHECK-DAG: error: verification failed: sum_is_seven {{.*}}[reason=counterexample]

// Below zero the hypothesis is empty: a claim that fails for negative n is
// refuted there.
cppverify::proof void closed_form_everywhere(int n)
  cppverify::pre(n <= 1000)
  cppverify::post(2 * sum(n) == n * (n + 1))
{
}
// CHECK-DAG: error: verification failed: closed_form_everywhere {{.*}}(counterexample: n [ssa=n_0] [type=i32] = -{{[0-9]+}})
