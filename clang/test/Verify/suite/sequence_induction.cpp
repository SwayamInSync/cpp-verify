// RUN: not %cpp-verify --timeout=20000 %s 2>&1 | FileCheck %s
//
// Induction over sequences is written by the user: a recursive proof
// function whose decreases clause is the length, citing itself on a shorter
// sequence. A stated equality of sequences is proved element by element, so
// it serves as a hint where the solver needs one.

#include <cppverify.h>
using cppverify::seq;

spec int total(seq s)
  decreases(s.len())
{
  return s.len() <= 0 ? 0 : total(s.subrange(0, s.len() - 1)) + s[s.len() - 1];
}
// CHECK-DAG: Verified: spec decreases: total

proof void total_concat(seq s, seq t)
  post(total(s + t) == total(s) + total(t))
  decreases(t.len())
{
  if (t.len() > 0)
    total_concat(s, t.subrange(0, t.len() - 1));
}
// CHECK-DAG: Verified: total_concat [backend=z3]

proof void total_concat_wrong(seq s, seq t)
  post(total(s + t) == total(s) + total(t) + 1)
  decreases(t.len())
{
  if (t.len() > 0)
    total_concat_wrong(s, t.subrange(0, t.len() - 1));
}
// CHECK-DAG: error: verification failed: total_concat_wrong [{{.*}}::postcondition@[[@LINE-6]]:{{[0-9]+}}] (counterexample: {{.*}}) [backend=z3] [reason=counterexample]

spec int count(seq s, int x)
  decreases(s.len())
{
  return s.len() <= 0
             ? 0
             : count(s.subrange(0, s.len() - 1), x) +
                   (s[s.len() - 1] == x ? 1 : 0);
}
// CHECK-DAG: Verified: spec decreases: count

proof void count_concat(seq s, seq t, int x)
  post(count(s + t, x) == count(s, x) + count(t, x))
  decreases(t.len())
{
  if (t.len() > 0)
    count_concat(s, t.subrange(0, t.len() - 1), x);
}
// CHECK-DAG: Verified: count_concat [backend=z3]

// reverse(s) is reverse(tail).push(s[0]); the stated equality splits s.
proof void count_reverse(seq s, int x)
  post(count(s.reverse(), x) == count(s, x))
  decreases(s.len())
{
  if (s.len() > 0) {
    seq tail = s.subrange(1, s.len());
    count_reverse(tail, x);
    count_concat(cppverify::seq_of(s[0]), tail, x);
    contract_assert(cppverify::seq_of(s[0]) + tail == s);
  }
}
// CHECK-DAG: Verified: count_reverse [backend=z3]

proof void reverse_index(seq s, long long k)
  pre(0 <= k && k < s.len())
  post(s.reverse()[k] == s[s.len() - 1 - k])
  decreases(s.len())
{
  if (k < s.len() - 1)
    reverse_index(s.subrange(1, s.len()), k);
}
// CHECK-DAG: Verified: reverse_index [backend=z3]

// The library's own termination checks are not reported.
// CHECK-NOT: post: reverse
