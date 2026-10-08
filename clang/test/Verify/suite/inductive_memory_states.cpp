// RUN: not %cpp-verify --timeout=10000 %s -- 2>&1 | FileCheck %s
//
// An inductive predicate that reads memory is a function of the memory state
// it is applied in. Each application's unfolding reads memory where the
// application does, and applications in different states have facts of
// their own.

#include <cppverify.h>
using cppverify::valid;

cppverify::spec bool linked(const int *next, int n, int i, int j)
  cppverify::inductive
  cppverify::reads(next, n)
{
  return i == j || (0 <= i && i < n && linked(next, n, next[i], j));
}

// After next[0] = 0, index 0 points to itself forever, so linked(next, 2, 0,
// 1) is false. An unfolding that read next[0] before the store proved it.
void stale(int *next)
  cppverify::pre(valid(next, 2) && next[0] == 1 && next[1] == 1)
  cppverify::modifies(next[0 : 2])
{
  cppverify::check(linked(next, 2, 1, 1));
  next[0] = 0;
  cppverify::check(linked(next, 2, 0, 1));
}
// CHECK-DAG: error: verification failed: stale {{.*}}[reason=counterexample]

// The same application before and after a store are two facts.
void both_states(int *next)
  cppverify::pre(valid(next, 2) && next[0] == 1 && next[1] == 1)
  cppverify::modifies(next[0 : 2])
{
  cppverify::check(linked(next, 2, 0, 1));
  next[0] = 0;
  cppverify::check(!linked(next, 2, 0, 1));
}
// It holds, by the least fixpoint: index 0 points to itself forever.
// CHECK-DAG: Unresolved: both_states

// After next[0] = 1, linked(next, 2, 0, 1) holds, so its negation fails.
void relinked_wrong(int *next)
  cppverify::pre(valid(next, 2) && next[0] == 0 && next[1] == 0)
  cppverify::modifies(next[0 : 2])
{
  next[0] = 1;
  cppverify::check(!linked(next, 2, 0, 1));
}
// CHECK-DAG: error: verification failed: relinked_wrong {{.*}}[reason=counterexample]
