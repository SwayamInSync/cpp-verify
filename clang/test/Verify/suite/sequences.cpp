// RUN: not %cpp-verify --timeout=20000 %s 2>&1 | FileCheck %s
// RUN: not %cpp-verify --timeout=20000 --diagnostics-format=json %s 2>/dev/null \
// RUN:   | FileCheck %s --check-prefix=JSON
// RUN: %cpp-verify --lower-only --dump-ir=3,4 %s 2>&1 \
// RUN:   | FileCheck %s --check-prefix=VC
// RUN: not %cpp-verify --obligation-out=%t.obligations %s > /dev/null 2>&1
// RUN: not %cpp-verify --timeout=20000 --obligation-in=%t.obligations 2>&1 \
// RUN:   | FileCheck %s --check-prefix=REPLAY
//
// cppverify::seq is a finite sequence of mathematical integers for
// contracts, ghost code, and spec and proof functions. Every operation is
// total: an index outside [0, len()) reads 0, an update there changes
// nothing, and subrange clamps its bounds. A ghost sequence can record what
// a loop has seen; its invariants quantify over the elements.

#include <cppverify.h>
using cppverify::seq;

proof void basics(seq s, int x)
{
  contract_assert(s.push(x).len() == s.len() + 1);
  contract_assert(s.push(x)[s.len()] == x);
  contract_assert(cppverify::seq_empty().len() == 0);
  contract_assert(cppverify::seq_of(x)[0] == x);
  contract_assert(s + cppverify::seq_of(x) == s.push(x));
  contract_assert(s.push(x).contains(x));
  contract_assert(s.len() >= 0);
}
// CHECK-DAG: Verified: basics

proof void total_operations(seq s)
  pre(s.len() == 3)
{
  contract_assert(s[-1] == 0 && s[3] == 0);
  contract_assert(s.update(5, 1) == s);
  contract_assert(s.update(1, 9)[1] == 9);
  contract_assert(s.update(1, 9)[0] == s[0]);
  contract_assert(s.subrange(-3, 9) == s);
  contract_assert(s.subrange(2, 1).len() == 0);
  contract_assert(s.subrange(1, 3)[0] == s[1]);
}
// CHECK-DAG: Verified: total_operations

// An extract of a concatenation splits at the boundary.
proof void drop_last_of_concat(seq s, seq t)
  pre(t.len() > 0)
  post((s + t).subrange(0, (s + t).len() - 1) == s + t.subrange(0, t.len() - 1))
  post((s + t).subrange(s.len(), (s + t).len()) == t)
{
}
// CHECK-DAG: Verified: drop_last_of_concat

// The counterexample is a sequence the certifier checked exactly.
proof void elements_differ(seq s)
  pre(s.len() == 2)
{
  contract_assert(s[0] == s[1]);
}
// CHECK-DAG: error: verification failed: elements_differ [{{.*}}::assertion@[[@LINE-2]]:3] (counterexample: s [ssa=s_0] [type=seq] = [{{-?[0-9]+}}, {{-?[0-9]+}}]) [backend=z3] [reason=counterexample]
// JSON-DAG: "function":"elements_differ"{{.*}}"model":[{"name":"s","sort":"seq","source":{{.*}},"ssa_name":"s_0","value":"[{{-?[0-9]+}}, {{-?[0-9]+}}]"}]

// Beyond its length a sequence reads 0, so finitely many indices decide an
// unbounded quantifier over its elements.
proof void unbounded_elements(seq s)
  pre(s.len() == 3)
{
  contract_assert(forall(k, s[k] >= 0));
}
// CHECK-DAG: error: verification failed: unbounded_elements [{{.*}}::assertion@[[@LINE-2]]:3] (counterexample: s [ssa=s_0] [type=seq] = [{{.*}}-{{[0-9]+.*}}]) [backend=z3] [reason=counterexample]

proof void unbounded_holds(seq s)
  pre(forall(k, 0, s.len(), s[k] >= 0))
{
  contract_assert(forall(k, s[k] >= 0));
}
// CHECK-DAG: Verified: unbounded_holds

// A recursive spec over a sequence terminates by its length.
spec int sum(seq s)
  decreases(s.len())
{
  return s.len() <= 0 ? 0 : sum(s.subrange(0, s.len() - 1)) + s[s.len() - 1];
}
// CHECK-DAG: Verified: spec decreases: sum

proof void sum_push(seq s, int x)
  post(sum(s.push(x)) == sum(s) + x)
{
}
// CHECK-DAG: Verified: sum_push

proof void sum_push_wrong(seq s, int x)
  post(sum(s.push(x)) == sum(s))
{
}
// CHECK-DAG: error: verification failed: sum_push_wrong [{{.*}}::postcondition@[[@LINE-3]]:{{[0-9]+}}] (counterexample: {{.*}}x [ssa=x_0] [type=i32] = {{-?[1-9][0-9]*}}) [backend=z3] [reason=counterexample]

spec bool valid(const int *p, int n) { return true; }

int count_positive(const int *a, int n)
  pre(valid(a, n) && n >= 0 && n <= 1000)
  post(0 <= result && result <= n)
{
  ghost seq seen = cppverify::seq_empty();
  int c = 0;
  for (int i = 0; i < n; i = i + 1)
    invariant(0 <= i && i <= n && 0 <= c && c <= i)
    invariant(seen.len() == i)
    invariant(forall(k, 0, i, seen[k] == a[k]))
    decreases(n - i)
  {
    if (a[i] > 0)
      c = c + 1;
    ghost { seen = seen.push(a[i]); }
  }
  contract_assert(forall(k, 0, n, seen[k] == a[k]));
  return c;
}
// CHECK-DAG: Verified: count_positive

void ghost_loop_wrong(int n)
  pre(n >= 1 && n <= 100)
{
  ghost seq s = cppverify::seq_empty();
  int i = 0;
  while (i < n)
    invariant(0 <= i && i <= n)
    invariant(s.len() == i)
    decreases(n - i)
  {
    ghost { s = s.push(i); }
    i = i + 1;
  }
  contract_assert(s[0] == 1);
}
// CHECK-DAG: error: verification failed: ghost_loop_wrong [{{.*}}::assertion@[[@LINE-2]]:3] (counterexample: {{.*}}s [ssa=s_2] [type=seq] = [{{-?[0-9]+}}]{{.*}}) [backend=z3] [reason=counterexample]

// REPLAY-DAG: Verified: basics
// REPLAY-DAG: Verified: count_positive
// REPLAY-DAG: error: verification failed: elements_differ
// REPLAY-DAG: error: verification failed: ghost_loop_wrong

// VC-LABEL: vc basics
// VC: features {{.*}}sequences
// VC: seq.push : seq
// VC-LABEL: vc count_positive
// VC: seq.index : int
// VC: (define-fun-rec cppverify.cell_i32 ((x Int)) Int
// VC: (define-fun-rec cppverify.seq_at ((s (Seq Int)) (i Int)) Int
