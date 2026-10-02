// RUN: not %cpp-verify --timeout=3000 --profile-quantifiers %s 2>&1 | FileCheck %s
// RUN: not %cpp-verify --timeout=3000 --profile-quantifiers --diagnostics-format=json %s 2>/dev/null | FileCheck %s --check-prefix=JSON
// RUN: %cpp-verify --lower-only --dump-ir=3 %s 2>&1 | FileCheck %s --check-prefix=VC
//
// trigger(term) in a quantifier body makes term the pattern that
// instantiates the quantifier: a memory read, a collection read, or a call of
// a recursive spec function that mentions a quantified variable. Other marks
// are ignored with a warning. --profile-quantifiers reports, for a query that
// stays unresolved, how often each quantifier was instantiated.

#include <cppverify.h>

spec bool valid(const int *p, int n) { return true; }

void positive(const int *a, int n)
  pre(valid(a, n) && n >= 1 && n <= 1000)
  pre(forall(k, 0, n, trigger(a[k]) > 0))
{
  contract_assert(a[n - 1] > 0);
}
// CHECK-DAG: Verified: positive

spec int twice(int x) { return 2 * x; }

void ignored_marks(const int *a, int n)
  pre(valid(a, n) && n >= 1 && n <= 1000)
  pre(forall(k, 0, n, trigger(k + 1) > 0))
  pre(forall(k, 0, n, trigger(a[0]) == 1 || k >= 0))
  pre(forall(k, 0, 10, trigger(twice(k)) == 2 * k))
{
}
// CHECK-DAG: warning: trigger(...) is ignored: only a memory read, a collection read, or a spec function call can trigger a quantifier
// CHECK-DAG: warning: trigger(...) is ignored: the term mentions no quantified variable
// CHECK-DAG: warning: trigger(...) is ignored: a call of a non-recursive spec function is replaced by its body; mark a term of the body instead
// CHECK-DAG: Verified: ignored_marks

// A trigger that feeds itself: each instance makes a new matching term.
spec int g(int n)
  decreases(n)
{
  return n <= 0 ? 0 : g(n - 1);
}

void matching_loop(int a)
  pre(forall(k, trigger(g(k)) == g(k + 1) + 1))
{
  ghost { hide(g); }
  contract_assert(g(a) > 100);
}
// CHECK-DAG: Unresolved: matching_loop
// CHECK-DAG: note: the quantifier at [[@LINE-6]]:7 was instantiated {{[0-9]+}} times, up to generation {{[0-9]+}}
// JSON-DAG: "function":"matching_loop"{{.*}}"quantifier_profile":[{"column":7,"instances":{{[0-9]+}},"line":[[@LINE-7]],

// A collection read can trigger; another collection operation cannot.
proof void sequence_trigger(cppverify::seq s)
  pre(forall(k, 0, s.len(), trigger(s[k]) > 0))
  pre(forall(k, 0, 3, trigger(s.push(k).len()) > 0))
{
  contract_assert(s.len() == 0 || s[s.len() - 1] > 0);
}
// CHECK-DAG: warning: trigger(...) is ignored: only a memory read, a collection read, or a spec function call can trigger a quantifier
// CHECK-DAG: Verified: sequence_trigger

// A program may still name a function trigger.
spec int trigger(int x) { return x + 0; }

void own_trigger(int n)
  pre(n >= 0 && n < 100)
{
  contract_assert(forall(k, 0, n, trigger(k) == k));
}
// CHECK-DAG: Verified: own_trigger

// VC-LABEL: vc positive
// VC: forall
// VC: trigger
// VC-NEXT: heap_select
