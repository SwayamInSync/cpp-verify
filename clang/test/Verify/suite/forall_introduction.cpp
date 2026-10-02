// RUN: not %cpp-verify --timeout=30000 %s 2>&1 | FileCheck %s
// RUN: not %cpp-verify --lower-only %S/Inputs/forall_introduction_assign.cpp 2>&1 \
// RUN:   | FileCheck %S/Inputs/forall_introduction_assign.cpp --check-prefix=ASSIGN
//
// contract_assert(forall(k, lo, hi, P)) by { proof } proves P for one
// arbitrary k in [lo, hi), which the proof may read but not assign; the
// forall then holds (universal generalization, Verus's assert forall ... by).

#include <cppverify.h>
using cppverify::valid;

proof void pair_ordered(const int *a, int n, int i, int j)
  pre(valid(a, n) && n <= 1000 && 0 <= i && i <= j && j < n)
  pre(forall(k, 0, n - 1, a[k] <= a[k + 1]))
  post(a[i] <= a[j])
  decreases(j - i)
{
  if (i < j)
    pair_ordered(a, n, i, j - 1);
}
// CHECK-DAG: Verified: pair_ordered

proof void below_last(const int *a, int n)
  pre(valid(a, n) && n >= 1 && n <= 1000)
  pre(forall(k, 0, n - 1, a[k] <= a[k + 1]))
  post(forall(k, 0, n, a[k] <= a[n - 1]))
{
  contract_assert(forall(k, 0, n, a[k] <= a[n - 1])) by {
    pair_ordered(a, n, k, n - 1);
  }
}
// CHECK-DAG: Verified: below_last

// The last element is not strictly above itself.
proof void strictly_below_last(const int *a, int n)
  pre(valid(a, n) && n >= 1 && n <= 1000)
  pre(forall(k, 0, n - 1, a[k] <= a[k + 1]))
{
  contract_assert(forall(k, 0, n, a[k] < a[n - 1])) by {
    pair_ordered(a, n, k, n - 1);
  }
}
// CHECK-DAG: error: verification failed: strictly_below_last [{{.*}}::assertion@[[@LINE-4]]:3] (counterexample: {{.*}}) [backend=z3] [reason=counterexample]

// Without bounds the variable ranges over every integer.
proof void squares(int m)
{
  contract_assert(forall(x, x * x >= 0)) by {
    contract_assert(x * x >= 0);
  }
}
// CHECK-DAG: Verified: squares
