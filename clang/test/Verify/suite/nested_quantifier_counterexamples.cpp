// RUN: not %cpp-verify --timeout=30000 %s -- 2>&1 | FileCheck %s
//
// A counterexample to nested quantifiers is checked exactly: with the model
// fixed, reads are constant pieces and the claim is Presburger arithmetic.

#include <cppverify.h>
using cppverify::seq;
using cppverify::valid;

// The largest element has no larger one.
cppverify::proof void every_has_larger(seq s)
  cppverify::pre(s.len() == 3)
{
  cppverify::check(cppverify::forall(i, !(0 <= i && i < s.len()) ||
                                cppverify::exists(j, 0 <= j && j < s.len() && s[j] > s[i])));
}
// CHECK-DAG: error: verification failed: every_has_larger [{{.*}}::assertion@[[@LINE-3]]:3] (counterexample: s [ssa=s_0] [type=seq] = [{{.*}}]) [backend=z3] [reason=counterexample]

cppverify::proof void every_has_no_smaller(seq s)
  cppverify::pre(s.len() >= 1 && s.len() <= 3)
{
  cppverify::check(cppverify::forall(i, !(0 <= i && i < s.len()) ||
                                cppverify::exists(j, 0 <= j && j < s.len() && s[j] >= s[i])));
}
// CHECK-DAG: Verified: every_has_no_smaller

int max_index(const int *a, int n)
  cppverify::pre(valid(a, n) && n >= 1 && n <= 100)
  cppverify::post(cppverify::forall(k, !(0 <= k && k < n) ||
                     cppverify::exists(m, 0 <= m && m < n && a[m] > a[k])))
{
  return 0;
}
// CHECK-DAG: error: verification failed: max_index [{{.*}}::postcondition@{{.*}}] (counterexample: {{.*}}) [backend=z3] [reason=counterexample]

// Distinct elements repeat nowhere.
cppverify::proof void some_repeated(seq s)
  cppverify::pre(s.len() == 3)
{
  cppverify::check(cppverify::exists(i, 0 <= i && i < s.len() &&
                               cppverify::exists(j, 0 <= j && j < s.len() && i != j &&
                                             s[i] == s[j])));
}
// CHECK-DAG: error: verification failed: some_repeated [{{.*}}::assertion@[[@LINE-4]]:3] (counterexample: s [ssa=s_0] [type=seq] = [{{.*}}]) [backend=z3] [reason=counterexample]

// A product of bound variables is outside Presburger arithmetic, but a
// witness decides the claim: no j makes 0 * j == 6.
cppverify::proof void not_all_products_even(int n)
  cppverify::pre(n == 3)
{
  cppverify::check(cppverify::forall(i, cppverify::exists(j, i * j == 2 * n)));
}
// CHECK-DAG: error: verification failed: not_all_products_even [{{.*}}::assertion@[[@LINE-2]]:3] (counterexample: n [ssa=n_0] [type=i32] = 3) [backend=z3] [reason=counterexample]

// Refuting this needs every value of i: no witness can, and i * j is no
// linear term.
cppverify::proof void no_opposite_factors(int n)
  cppverify::pre(n == 2)
{
  cppverify::check(cppverify::exists(i, cppverify::exists(j, i * j == n && i + j == 0)));
}
// CHECK-DAG: Unresolved: no_opposite_factors [backend=z3] [reason={{counterexample.unchecked|solver.unknown|solver.timeout}}]
