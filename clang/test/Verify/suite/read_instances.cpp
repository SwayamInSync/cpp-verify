// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefixes=CHECK,Z3
// RUN: %cpp-verify --lower-only --dump-ir=4 %s 2>&1 | FileCheck %s --check-prefix=SMT
//
// A quantified fact about p[k] reads p + 4 * k. A solver matches it against
// the reads of the query, but its rewriter folds a read at a constant or
// compound index, p + 2 * 4, into p + 8, which the pattern p + 4 * k never
// matches. Each quantifier is therefore also stated at the indices of the
// query's closed reads with its base and stride: forall k. B is
// forall k. B && B(t), an equivalence, so no verdict changes.

#include <cppverify.h>
using cppverify::valid;

void constant_index(const int *p, int n)
  pre(valid(p, n) && n >= 3 && n <= 100)
  pre(forall(k, 0, n, p[k] >= 0))
{
  contract_assert(p[2] >= 0);
}
// CHECK-DAG: Verified: constant_index
// SMT: (or (not (and (<= 0 2) (< 2 n_0))) (>= a!5 0))
// SMT: (not (and a!1 a!6))

void first_and_deref(const int *p, int n)
  pre(valid(p, n) && n >= 3 && n <= 100)
  pre(forall(k, 0, n, p[k] >= 0))
{
  contract_assert(p[0] >= 0 && *p >= 0 && *(p + 2) >= 0);
}
// CHECK-DAG: Verified: first_and_deref

void next_index(const int *p, int n, int i)
  pre(valid(p, n) && n >= 3 && n <= 100 && 0 <= i && i < n - 1)
  pre(forall(k, 0, n, p[k] >= 0))
{
  contract_assert(p[i + 1] >= 0 && p[i] >= 0);
}
// CHECK-DAG: Verified: next_index

void long_elements(const long *p, int n)
  pre(valid(p, n) && n >= 3 && n <= 100)
  pre(forall(k, 0, n, p[k] >= 0))
{
  contract_assert(p[2] >= 0);
}
// CHECK-DAG: Verified: long_elements

// Two instances of an adjacent-pairs fact chain.
void adjacent_chain(const int *p, int n)
  pre(valid(p, n) && n >= 6 && n <= 100)
  pre(forall(k, 0, n - 1, p[k] <= p[k + 1]))
{
  contract_assert(p[1] <= p[3]);
}
// CHECK-DAG: Verified: adjacent_chain

// A witness for an existential postcondition.
void witness(const int *p, int n)
  pre(valid(p, n) && n >= 3 && n <= 100 && p[2] == 7)
  post(exists(k, 0, n, p[k] == 7))
{
}
// CHECK-DAG: Verified: witness

// The instances are equivalences: false claims still fail.
void too_strong(const int *p, int n)
  pre(valid(p, n) && n >= 3 && n <= 100)
  pre(forall(k, 0, n, p[k] >= 0))
{
  contract_assert(p[2] >= 1);
}
// Z3-DAG: error: verification failed: too_strong [{{.*}}::assertion@[[@LINE-2]]:3]

void outside_range(const int *p, int n)
  pre(valid(p, n + 1) && n >= 3 && n <= 100)
  pre(forall(k, 0, n, p[k] >= 0))
{
  contract_assert(p[n] >= 0);
}
// Z3-DAG: error: verification failed: outside_range [{{.*}}::assertion@[[@LINE-2]]:3]

void wrong_witness(const int *p, int n)
  pre(valid(p, n) && n >= 3 && n <= 100 && p[2] == 7)
  post(exists(k, 3, n, p[k] == 7))
{
}
// Z3-DAG: error: verification failed: wrong_witness [{{.*}}::postcondition@[[@LINE-3]]:8]
