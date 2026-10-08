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

cppverify::proof void basics(seq s, int x)
{
  cppverify::check(s.push(x).len() == s.len() + 1);
  cppverify::check(s.push(x)[s.len()] == x);
  cppverify::check(cppverify::seq_empty().len() == 0);
  cppverify::check(cppverify::seq_of(x)[0] == x);
  cppverify::check(s + cppverify::seq_of(x) == s.push(x));
  cppverify::check(s.push(x).contains(x));
  cppverify::check(s.len() >= 0);
}
// CHECK-DAG: Verified: basics

cppverify::proof void total_operations(seq s)
  cppverify::pre(s.len() == 3)
{
  cppverify::check(s[-1] == 0 && s[3] == 0);
  cppverify::check(s.update(5, 1) == s);
  cppverify::check(s.update(1, 9)[1] == 9);
  cppverify::check(s.update(1, 9)[0] == s[0]);
  cppverify::check(s.subrange(-3, 9) == s);
  cppverify::check(s.subrange(2, 1).len() == 0);
  cppverify::check(s.subrange(1, 3)[0] == s[1]);
}
// CHECK-DAG: Verified: total_operations

// update and reverse are specs of <cppverify.h> over the other operations.
// A stated equality of sequences is proved element by element.
cppverify::proof void update_twice(seq s)
  cppverify::pre(s.len() == 3)
{
  cppverify::check(s.update(1, 9).len() == 3);
  cppverify::check(s.update(1, 9).update(1, s[1]) == s);
}
// CHECK-DAG: Verified: update_twice

cppverify::proof void update_wrong(seq s)
  cppverify::pre(s.len() == 3)
{
  cppverify::check(s.update(1, 9)[2] == 9);
}
// CHECK-DAG: error: verification failed: update_wrong [{{.*}}::assertion@[[@LINE-2]]:3] (counterexample: s [ssa=s_0] [type=seq] = [{{-?[0-9]+}}, {{-?[0-9]+}}, {{-?[0-9]+}}]) [backend=z3] [reason=counterexample]

cppverify::proof void reverse_small()
{
  cppverify::ghost seq s = cppverify::seq_of(1).push(2).push(3);
  cppverify::check(s.reverse() == cppverify::seq_of(3).push(2).push(1));
}
// CHECK-DAG: Verified: reverse_small

// The model lists the elements in order.
cppverify::proof void reverse_wrong()
{
  cppverify::ghost seq s = cppverify::seq_of(1).push(2);
  cppverify::check(s.reverse()[0] == 1);
}
// CHECK-DAG: error: verification failed: reverse_wrong [{{.*}}::assertion@[[@LINE-2]]:3] (counterexample: s [ssa=s_1] [type=seq] = [1, 2]) [backend=z3] [reason=counterexample]

// reverse states its length; its elements need induction.
cppverify::proof void reverse_index(seq s, long long k)
  cppverify::pre(0 <= k && k < s.len())
  cppverify::post(s.reverse()[k] == s[s.len() - 1 - k])
  cppverify::decreases(s.len())
{
  if (k < s.len() - 1)
    reverse_index(s.subrange(1, s.len()), k);
}
// CHECK-DAG: Verified: reverse_index

// An extract of a concatenation splits at the boundary.
cppverify::proof void drop_last_of_concat(seq s, seq t)
  cppverify::pre(t.len() > 0)
  cppverify::post((s + t).subrange(0, (s + t).len() - 1) == s + t.subrange(0, t.len() - 1))
  cppverify::post((s + t).subrange(s.len(), (s + t).len()) == t)
{
}
// CHECK-DAG: Verified: drop_last_of_concat

// The counterexample is a sequence the certifier checked exactly.
cppverify::proof void elements_differ(seq s)
  cppverify::pre(s.len() == 2)
{
  cppverify::check(s[0] == s[1]);
}
// CHECK-DAG: error: verification failed: elements_differ [{{.*}}::assertion@[[@LINE-2]]:3] (counterexample: s [ssa=s_0] [type=seq] = [{{-?[0-9]+}}, {{-?[0-9]+}}]) [backend=z3] [reason=counterexample]
// JSON-DAG: "function":"elements_differ"{{.*}}"model":[{"name":"s","sort":"seq","source":{{.*}},"ssa_name":"s_0","value":"[{{-?[0-9]+}}, {{-?[0-9]+}}]"}]

// Beyond its length a sequence reads 0, so finitely many indices decide an
// unbounded quantifier over its elements.
cppverify::proof void unbounded_elements(seq s)
  cppverify::pre(s.len() == 3)
{
  cppverify::check(cppverify::forall(k, s[k] >= 0));
}
// CHECK-DAG: error: verification failed: unbounded_elements [{{.*}}::assertion@[[@LINE-2]]:3] (counterexample: s [ssa=s_0] [type=seq] = [{{.*}}-{{[0-9]+.*}}]) [backend=z3] [reason=counterexample]

cppverify::proof void unbounded_holds(seq s)
  cppverify::pre(cppverify::forall(k, 0, s.len(), s[k] >= 0))
{
  cppverify::check(cppverify::forall(k, s[k] >= 0));
}
// CHECK-DAG: Verified: unbounded_holds

// A recursive spec over a sequence terminates by its length.
cppverify::spec int sum(seq s)
  cppverify::decreases(s.len())
{
  return s.len() <= 0 ? 0 : sum(s.subrange(0, s.len() - 1)) + s[s.len() - 1];
}
// CHECK-DAG: Verified: spec decreases: sum

cppverify::proof void sum_push(seq s, int x)
  cppverify::post(sum(s.push(x)) == sum(s) + x)
{
}
// CHECK-DAG: Verified: sum_push

cppverify::proof void sum_push_wrong(seq s, int x)
  cppverify::post(sum(s.push(x)) == sum(s))
{
}
// CHECK-DAG: error: verification failed: sum_push_wrong [{{.*}}::postcondition@[[@LINE-3]]:{{[0-9]+}}] (counterexample: {{.*}}x [ssa=x_0] [type=i32] = {{-?[1-9][0-9]*}}) [backend=z3] [reason=counterexample]

cppverify::spec bool valid(const int *p, int n) { return true; }

int count_positive(const int *a, int n)
  cppverify::pre(valid(a, n) && n >= 0 && n <= 1000)
  cppverify::post(0 <= cppverify::result && cppverify::result <= n)
{
  cppverify::ghost seq seen = cppverify::seq_empty();
  int c = 0;
  for (int i = 0; i < n; i = i + 1)
    cppverify::invariant(0 <= i && i <= n && 0 <= c && c <= i)
    cppverify::invariant(seen.len() == i)
    cppverify::invariant(cppverify::forall(k, 0, i, seen[k] == a[k]))
    cppverify::decreases(n - i)
  {
    if (a[i] > 0)
      c = c + 1;
    cppverify::ghost { seen = seen.push(a[i]); }
  }
  cppverify::check(cppverify::forall(k, 0, n, seen[k] == a[k]));
  return c;
}
// CHECK-DAG: Verified: count_positive

void ghost_loop_wrong(int n)
  cppverify::pre(n >= 1 && n <= 100)
{
  cppverify::ghost seq s = cppverify::seq_empty();
  int i = 0;
  while (i < n)
    cppverify::invariant(0 <= i && i <= n)
    cppverify::invariant(s.len() == i)
    cppverify::decreases(n - i)
  {
    cppverify::ghost { s = s.push(i); }
    i = i + 1;
  }
  cppverify::check(s[0] == 1);
}
// CHECK-DAG: error: verification failed: ghost_loop_wrong [{{.*}}::assertion@[[@LINE-2]]:3] (counterexample: {{.*}}s [ssa=s_2] [type=seq] = [{{-?[0-9]+}}]{{.*}}) [backend=z3] [reason=counterexample]

// REPLAY-DAG: Verified: basics
// REPLAY-DAG: Verified: reverse_index
// REPLAY-DAG: Verified: count_positive
// REPLAY-DAG: error: verification failed: elements_differ
// REPLAY-DAG: error: verification failed: ghost_loop_wrong

// VC-LABEL: vc basics
// VC: features {{.*}}sequences
// VC: seq.push : seq
// VC-LABEL: vc update_twice
// VC: :pattern (((_ cppverify.seq_at 0) (seq.extract s_0 0 (- 1 0)) cppverify!k))
// VC: (= cppverify!t1 (seq.++ (seq.extract s_0 0 (- 1 0)) (seq.unit 9) a!1))
// VC: :pattern (((_ cppverify.seq_at 0) cppverify!t1 cppverify!k))
// VC: (forall ((__cppverify_ext0 Int))
// VC-LABEL: vc count_positive
// VC: seq.index : int
// VC: (define-fun-rec cppverify.cell_i32 ((x Int)) Int
// VC: (define-fun-rec cppverify.seq_at ((s (Seq Int)) (i Int)) Int
