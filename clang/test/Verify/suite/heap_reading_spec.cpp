// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify --check-ub %s 2>&1 | FileCheck %s --check-prefixes=CHECK,LOOP
// RUN: %cpp-verify --check-ub --lower-only --dump-ir=2 %s 2>&1 | FileCheck %s --check-prefix=PASSIVE
// RUN: %cpp-verify --check-ub --lower-only --dump-ir=3 %s 2>&1 | FileCheck %s --check-prefix=VC
// RUN: %cpp-verify --check-ub --lower-only --obligation-out=%t.cpv %s
// RUN: not %cpp-verify --obligation-in=%t.cpv 2>&1 | FileCheck %s --check-prefix=REPLAY

// Each heap-reading spec call reads the heap state a load at that point would.

spec bool valid(const int *p, int n) { return true; }
spec bool valid(int *p, int n) { return true; }

spec int sum(const int *p, int n)
  decreases(n)
{
  if (n <= 0)
    return 0;
  return sum(p, n - 1) + p[n - 1];
}

// VC: function {{.*}} sum math
// VC-NEXT: parameter __spec_heap heap
// VC-NEXT: parameter p pointer
// VC-NEXT: parameter n int
// VC: heap_select : bitvector32
// VC-NEXT: __spec_heap : heap

int total(const int *p, int n)
  pre(n >= 0 && n <= 1000 && valid(p, n))
  pre(forall(j, 0, n, -1000 <= p[j] && p[j] <= 1000))
  post(result == sum(p, n))
{
  int acc = 0;
  int i = 0;
  while (i < n)
    invariant(0 <= i && i <= n && acc == sum(p, i))
    invariant(-1000 * i <= acc && acc <= 1000 * i)
    decreases(n - i)
  {
    acc = acc + p[i];
    i = i + 1;
  }
  return acc;
}
// LOOP-DAG: Verified: total
// CVC5-DAG: {{Verified|Unresolved}}: total
// REPLAY-DAG: Verified: total
// VC: features {{.*}}heap-functions

int skip_first(const int *p, int n)
  pre(n >= 0 && n <= 1000 && valid(p, n))
  pre(forall(j, 0, n, -1000 <= p[j] && p[j] <= 1000))
  post(result == sum(p, n))
{
  int acc = 0;
  int i = 0;
  while (i < n)
    invariant(0 <= i && i <= n && acc == sum(p, i))
    invariant(-1000 * i <= acc && acc <= 1000 * i)
    decreases(n - i)
  {
    if (i > 0)
      acc = acc + p[i];
    i = i + 1;
  }
  return acc;
}
// LOOP-DAG: verification failed: skip_first
// CVC5-DAG: {{verification failed|Unresolved}}: skip_first
// REPLAY-DAG: verification failed: skip_first

void clear_first(int *p)
  pre(valid(p, 2))
  pre(-1000 <= p[0] && p[0] <= 1000 && -1000 <= p[1] && p[1] <= 1000)
  modifies(*p)
  post(sum(p, 2) == old(sum(p, 2)) - old(p[0]))
{
  ghost { reveal_with_fuel(sum, 3); }
  p[0] = 0;
}
// CHECK-DAG: Verified: clear_first
// REPLAY-DAG: Verified: clear_first

void clear_first_unchanged(int *p)
  pre(valid(p, 2))
  pre(-1000 <= p[0] && p[0] <= 1000 && -1000 <= p[1] && p[1] <= 1000)
  modifies(*p)
  post(sum(p, 2) == old(sum(p, 2)))
{
  ghost { reveal_with_fuel(sum, 3); }
  p[0] = 0;
}
// The post-state call reads the stored heap and old(...) the entry heap.
// PASSIVE-LABEL: passive clear_first_unchanged
// PASSIVE: heap_store __heap_0 -> __heap_1
// PASSIVE: spec_call sum reads __heap_1
// PASSIVE: spec_call sum reads __heap_0
// LOOP-DAG: verification failed: clear_first_unchanged
// cvc5 cannot check its model against sum's definition; the portfolio accepts
// its sat together with Z3's checked counterexample.
// CVC5ONLY-DAG: Unresolved: clear_first_unchanged {{.*}}[reason=spec.fuel]
// PORTFOLIO-DAG: verification failed: clear_first_unchanged
// REPLAY-DAG: verification failed: clear_first_unchanged

// A non-recursive heap-reading spec is inlined at each call.
spec int sum2(int *p)
{
  return p[0] + p[1];
}

int total2(int *p)
  pre(valid(p, 2))
  pre(-1000 <= p[0] && p[0] <= 1000 && -1000 <= p[1] && p[1] <= 1000)
  post(result == sum2(p))
{
  return p[0] + p[1];
}
// CHECK-DAG: Verified: total2

// A callee postcondition is instantiated in the heap of its call.
int caller(int *q)
  pre(valid(q, 2))
  modifies(*q)
  post(result == 12)
{
  q[0] = 5;
  q[1] = 7;
  return total2(q);
}
// CHECK-DAG: Verified: caller

int caller_stale(int *q)
  pre(valid(q, 2))
  pre(q[0] == 1 && q[1] == 1)
  modifies(*q)
  post(result == 2)
{
  q[0] = 5;
  q[1] = 7;
  return total2(q);
}
// CHECK-DAG: verification failed: caller_stale

struct Pair {
  int first;
  int second;
};

spec int pair_sum(const Pair *pair) {
  return pair->first + pair->second;
}

int read_pair(Pair *pair)
  pre(pair != nullptr && pair->first == 1 && pair->second == 2)
  post(result == pair_sum(pair))
{
  return 3;
}
// CHECK-DAG: Verified: read_pair

int read_pair_wrong(Pair *pair)
  pre(pair != nullptr && pair->first == 1 && pair->second == 2)
  post(result == pair_sum(pair))
{
  return 4;
}
// CHECK-DAG: verification failed: read_pair_wrong
