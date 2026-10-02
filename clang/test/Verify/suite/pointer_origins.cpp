// RUN: not %cpp-verify --timeout=30000 %s 2>&1 | FileCheck %s
// RUN: %cpp-verify --lower-only --dump-ir=1 %s 2>&1 \
// RUN:   | FileCheck %s --check-prefix=VCR
//
// Every pointer variable has origins: the objects it may address. Pointer
// arithmetic keeps them, assignment copies them, and branches and loops join
// them. An access or step must stay in its origin's object, a difference
// needs one origin, and a loop writes only its stores' origins.

#include <cppverify.h>
using cppverify::valid;

// A stepped position subtracted from its start, also in the measure.
int length_of(const char *s, int n)
  pre(valid(s, n) && n >= 1 && n <= 1000)
  post(0 <= result && result < n)
{
  const char *p = s;
  while (p < s + (n - 1) && *p != 0)
    invariant(s <= p && p <= s + (n - 1))
    decreases(s + (n - 1) - p)
  {
    p = p + 1;
  }
  return p - s;
}
// CHECK-DAG: Verified: length_of

// Two positions copied from one parameter.
int span(int *a, int n)
  pre(valid(a, n) && n >= 2 && n <= 1000)
  post(result == n - 1)
{
  int *lo = a;
  int *hi = a + (n - 1);
  return hi - lo;
}
// CHECK-DAG: Verified: span

// A parameter moved away from its entry value keeps its origin.
long moved(int *a, int n)
  pre(valid(a, n) && n >= 3 && n <= 100)
  post(result == 3)
{
  int *s = a;
  a = a + 3;
  return a - s;
}
// CHECK-DAG: Verified: moved

// A walking store frames the other parameter without an invariant; the
// walker stays a whole number of elements from a.
void keeps_other(int *a, int *b, int n)
  pre(valid(a, n) && n >= 0 && n <= 100 && b != nullptr)
  modifies(*a)
  post(*b == old(*b))
{
  int *q = a + n;
  while (q != a)
    invariant(a <= q && q <= a + n)
    decreases(q - a)
  {
    q = q - 1;
    *q = 0;
  }
}
// CHECK-DAG: Verified: keeps_other

// A reassigned parameter walks its entry object, inside modifies(*a).
void zero_param(int *a, int n, int *b)
  pre(valid(a, n) && n >= 0 && n <= 1000 && b != nullptr)
  modifies(*a)
  post(*b == old(*b))
{
  int k = n;
  while (k > 0)
    invariant(0 <= k && k <= n && a == old(a) + (n - k))
    decreases(k)
  {
    *a = 0;
    a = a + 1;
    k = k - 1;
  }
}
// CHECK-DAG: Verified: zero_param

// A walker chosen between two objects, tied to the choice.
void clear_chosen(int *a, int *b, int n, bool s)
  pre(valid(a, n) && valid(b, n) && n >= 1 && n <= 1000)
  modifies(*a, *b)
{
  int *q = s ? a : b;
  for (int i = 0; i < n; i = i + 1)
    invariant(0 <= i && i <= n && (s ? q == a + i : q == b + i))
    decreases(n - i)
  {
    *q = 0;
    q = q + 1;
  }
}
// CHECK-DAG: Verified: clear_chosen

// Only addresses: q may be one past a where b starts, while it came from a.
void clear_chosen_loose(int *a, int *b, int n, bool s)
  pre(valid(a, n) && valid(b, n) && n >= 1 && n <= 1000)
  modifies(*a, *b)
{
  int *q = s ? a : b;
  for (int i = 0; i < n; i = i + 1)
    invariant(0 <= i && i <= n && (q == a + i || q == b + i))
    decreases(n - i)
  {
    *q = 0;
    q = q + 1;
  }
}
// CHECK-DAG: error: verification failed: clear_chosen_loose [{{.*}}::bounds@[[@LINE-4]]:6]

long choice_diff(int *a, int *b, bool first)
  pre(a != nullptr && b != nullptr && first)
{
  int *p = first ? a : b;
  return p - a;
}
// CHECK-DAG: Verified: choice_diff

// p may come from b, which may or may not be in a's caller array.
long mixed(int *a, int *b, bool first)
  pre(a != nullptr && b != nullptr)
{
  int *p = first ? a : b;
  return p - a;
}
// CHECK-DAG: Unresolved: mixed [backend=z3] [reason=construct.unsupported]

// Stepping past the extent of a reassigned parameter.
void param_past(int *a)
  pre(valid(a, 2))
{
  a = a + 2;
  a = a + 1;
}
// CHECK-DAG: error: verification failed: param_past [{{.*}}::bounds@[[@LINE-2]]:9]

// One past a single object, even where another object may start.
void adjacent(int *a, int *b)
  pre(a != nullptr && b != nullptr)
  modifies(*a, *b)
{
  int *q = a + 1;
  *q = 0;
}
// CHECK-DAG: error: verification failed: adjacent [{{.*}}::bounds@[[@LINE-2]]:4]

// The walker does change its own object.
void walk_changes(int *a, int n)
  pre(valid(a, n) && n >= 1 && n <= 100)
  modifies(*a)
  post(a[0] == old(a[0]))
{
  int *q = a;
  for (int i = 0; i < n; i = i + 1)
    invariant(0 <= i && i <= n && q == a + i)
    decreases(n - i)
  {
    *q = 7;
    q = q + 1;
  }
}
// CHECK-DAG: error: verification failed: walk_changes [{{.*}}::postcondition@{{.*}}] (counterexample: {{.*}}) [backend=z3] [reason=counterexample]

// A chosen object may be either.
void chosen_changes(int *a, int *b, bool first)
  pre(a != nullptr && b != nullptr)
  modifies(*a, *b)
  post(*a == old(*a))
{
  int *p = first ? a : b;
  for (int i = 0; i < 1; i = i + 1)
    invariant(0 <= i && i <= 1)
    decreases(1 - i)
  {
    *p = 5;
  }
}
// CHECK-DAG: error: verification failed: chosen_changes [{{.*}}::postcondition@{{.*}}] (counterexample: {{.*}}first [ssa=first_0] [type=bool] = true{{.*}}) [backend=z3] [reason=counterexample]

// The companion naming q's origin, and the generated invariants.
// VCR-LABEL: fn clear_chosen
// VCR: assign q.__origin
// VCR: q.__origin
// VCR: %
