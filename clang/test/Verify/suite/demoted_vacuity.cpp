// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s
// RUN: not %cpp-verify --diagnostics-format=json %s -- 2>&1 | FileCheck %s --check-prefix=JSON
//
// That no execution reaches a claim is found from the facts of a query. A
// verdict demoted because a fact is not established loses each finding
// whose query may contain it: a definition that does not terminate can
// contradict itself, and whether a solver finds that says nothing about the
// program. A callee contract enters only after the entry state, so a finding
// about the entry state alone outlasts it.

cppverify::spec int loop(int n)
  cppverify::decreases(n)
{
  return loop(n) + 1;
}
// CHECK: error: spec decreases failed: loop

int uses_loop(int x)
  cppverify::post(cppverify::result == 0)
{
  cppverify::check(loop(x) > 0 || loop(x) <= 0);
  return 1;
}
// CHECK-NEXT: Unresolved: uses_loop [backend=z3] [reason=spec.termination] (relies on the definition of loop, whose termination is not established)

// The precondition holds for every x.
int loop_in_precondition(int x)
  cppverify::pre(loop(x) > 0 || loop(x) <= 0)
  cppverify::post(cppverify::result == 0)
{
  return 1;
}
// CHECK-NEXT: Unresolved: loop_in_precondition [backend=z3] [reason=spec.termination] (relies on the definition of loop, whose termination is not established)

int contradictory(int x)
  cppverify::post(cppverify::result == x && cppverify::result == x + 1)
{
  return x;
}
// CHECK-NEXT: error: verification failed: contradictory

int uses_contradictory(int x)
  cppverify::post(cppverify::result == 7)
{
  int r = contradictory(x);
  return r;
}
// CHECK-NEXT: Unresolved: uses_contradictory [backend=z3] [reason=callee.contract] (relies on the contract of contradictory, which is not established)

// A contract that fails but does not contradict itself.
int wrong_seven(int x)
  cppverify::post(cppverify::result == 7)
{
  return x;
}
// CHECK-NEXT: error: verification failed: wrong_seven

[[cppverify::trusted]] void claims_nonnegative(int x)
  cppverify::post(x >= 0);
// CHECK-NEXT: Trusted: claims_nonnegative

int contradicted(int x)
  cppverify::post(cppverify::result == 7)
{
  if (x < 0)
    claims_nonnegative(x);
  return wrong_seven(x);
}
// CHECK-NEXT: Unresolved: contradicted [backend=z3] [reason=callee.contract] (relies on the contract of wrong_seven, which is not established)

int unsatisfiable_and_relying(int x)
  cppverify::pre(x > 0 && x < 0)
  cppverify::post(cppverify::result == 7)
{
  return contradictory(x);
}
// CHECK-NEXT: Unresolved: unsatisfiable_and_relying [backend=z3] [vacuous] [reason=callee.contract] (relies on the contract of contradictory, which is not established)
// CHECK-NEXT: warning: unsatisfiable_and_relying: the precondition is unsatisfiable, so every claim about it holds vacuously

int never_applies(int x)
  cppverify::behavior(impossible, x > 0 && x < 0)
    cppverify::post(cppverify::result == 7)
  cppverify::post(cppverify::result == 7)
{
  return wrong_seven(x);
}
// CHECK-NEXT: Unresolved: never_applies [backend=z3] [reason=callee.contract] (relies on the contract of wrong_seven, which is not established)
// CHECK-NEXT: warning: never_applies: behavior impossible never applies

// A proof that stands keeps its finding.
int unsatisfiable(int x)
  cppverify::pre(x > 0 && x < 0)
  cppverify::post(cppverify::result == 1)
{
  return 0;
}
// CHECK-NEXT: Verified: unsatisfiable [backend=z3] [vacuous]
// CHECK-NEXT: warning: unsatisfiable: the precondition is unsatisfiable, so every claim about it holds vacuously
// CHECK-NEXT: Summary: {{.*}}
// CHECK-NOT: {{.}}

// JSON: "function":"uses_loop"
// JSON-NOT: vacuous
// JSON: "function":"unsatisfiable_and_relying"{{.*}}"vacuous":true
// JSON: "message":"unsatisfiable_and_relying: the precondition is unsatisfiable
// JSON-NOT: "vacuous"
// JSON: "function":"unsatisfiable"{{.*}}"vacuous":true
