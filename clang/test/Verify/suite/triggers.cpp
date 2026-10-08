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

cppverify::spec bool valid(const int *p, int n) { return true; }

void positive(const int *a, int n)
  cppverify::pre(valid(a, n) && n >= 1 && n <= 1000)
  cppverify::pre(cppverify::forall(k, 0, n, cppverify::trigger(a[k]) > 0))
{
  cppverify::check(a[n - 1] > 0);
}
// CHECK-DAG: Verified: positive

cppverify::spec int twice(int x) { return 2 * x; }

void ignored_marks(const int *a, int n)
  cppverify::pre(valid(a, n) && n >= 1 && n <= 1000)
  cppverify::pre(cppverify::forall(k, 0, n, cppverify::trigger(k + 1) > 0))
  cppverify::pre(cppverify::forall(k, 0, n, cppverify::trigger(a[0]) == 1 || k >= 0))
  cppverify::pre(cppverify::forall(k, 0, 10, cppverify::trigger(twice(k)) == 2 * k))
{
}
// CHECK-DAG: warning: cppverify::trigger(...) is ignored: only a memory read, a collection read, or a spec function call can trigger a quantifier
// CHECK-DAG: warning: cppverify::trigger(...) is ignored: the term mentions no quantified variable
// CHECK-DAG: warning: cppverify::trigger(...) is ignored: a call of a non-recursive spec function is replaced by its body; mark a term of the body instead
// CHECK-DAG: Verified: ignored_marks

// A trigger that feeds itself: each instance makes a new matching term.
cppverify::spec int g(int n)
  cppverify::decreases(n)
{
  return n <= 0 ? 0 : g(n - 1);
}

void matching_loop(int a)
  cppverify::pre(cppverify::forall(k, cppverify::trigger(g(k)) == g(k + 1) + 1))
{
  cppverify::ghost { cppverify::hide(g); }
  cppverify::check(g(a) > 100);
}
// CHECK-DAG: Unresolved: matching_loop
// CHECK-DAG: note: the quantifier at [[@LINE-6]]:18 was instantiated {{[0-9]+}} times, up to generation {{[0-9]+}}
// JSON-DAG: "function":"matching_loop"{{.*}}"quantifier_profile":[{"column":18,"instances":{{[0-9]+}},"line":[[@LINE-7]],

// A collection read can trigger; another collection operation cannot.
cppverify::proof void sequence_trigger(cppverify::seq s)
  cppverify::pre(cppverify::forall(k, 0, s.len(), cppverify::trigger(s[k]) > 0))
  cppverify::pre(cppverify::forall(k, 0, 3, cppverify::trigger(s.push(k).len()) > 0))
{
  cppverify::check(s.len() == 0 || s[s.len() - 1] > 0);
}
// CHECK-DAG: warning: cppverify::trigger(...) is ignored: only a memory read, a collection read, or a spec function call can trigger a quantifier
// CHECK-DAG: Verified: sequence_trigger

// A program may still name a function trigger.
cppverify::spec int trigger(int x) { return x + 0; }

void own_trigger(int n)
  cppverify::pre(n >= 0 && n < 100)
{
  cppverify::check(cppverify::forall(k, 0, n, cppverify::trigger(k) == k));
}
// CHECK-DAG: Verified: own_trigger

// VC-LABEL: vc positive
// VC: forall
// VC: trigger
// VC-NEXT: heap_select
