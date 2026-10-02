// RUN: not %cpp-verify --timeout=30000 %s 2>&1 | FileCheck %s
//
// A counterexample to nested quantifiers is checked exactly: with the model
// fixed, reads are constant pieces and the claim is Presburger arithmetic.

#include <cppverify.h>
using cppverify::seq;
using cppverify::valid;

// The largest element has no larger one.
proof void every_has_larger(seq s)
  pre(s.len() == 3)
{
  contract_assert(forall(i, !(0 <= i && i < s.len()) ||
                                exists(j, 0 <= j && j < s.len() && s[j] > s[i])));
}
// CHECK-DAG: error: verification failed: every_has_larger [{{.*}}::assertion@[[@LINE-3]]:3] (counterexample: s [ssa=s_0] [type=seq] = [{{.*}}]) [backend=z3] [reason=counterexample]

proof void every_has_no_smaller(seq s)
  pre(s.len() >= 1 && s.len() <= 3)
{
  contract_assert(forall(i, !(0 <= i && i < s.len()) ||
                                exists(j, 0 <= j && j < s.len() && s[j] >= s[i])));
}
// CHECK-DAG: Verified: every_has_no_smaller

int max_index(const int *a, int n)
  pre(valid(a, n) && n >= 1 && n <= 100)
  post(forall(k, !(0 <= k && k < n) ||
                     exists(m, 0 <= m && m < n && a[m] > a[k])))
{
  return 0;
}
// CHECK-DAG: error: verification failed: max_index [{{.*}}::postcondition@{{.*}}] (counterexample: {{.*}}) [backend=z3] [reason=counterexample]

// Distinct elements repeat nowhere.
proof void some_repeated(seq s)
  pre(s.len() == 3)
{
  contract_assert(exists(i, 0 <= i && i < s.len() &&
                               exists(j, 0 <= j && j < s.len() && i != j &&
                                             s[i] == s[j])));
}
// CHECK-DAG: error: verification failed: some_repeated [{{.*}}::assertion@[[@LINE-4]]:3] (counterexample: s [ssa=s_0] [type=seq] = [{{.*}}]) [backend=z3] [reason=counterexample]

// A product of bound variables is outside the decided fragment.
proof void not_all_products_even(int n)
  pre(n == 3)
{
  contract_assert(forall(i, exists(j, i * j == 2 * n)));
}
// CHECK-DAG: Unresolved: not_all_products_even [backend=z3] [reason={{counterexample.unchecked|solver.unknown|solver.timeout}}]
