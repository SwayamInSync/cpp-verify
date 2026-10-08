// RUN: %cpp-verify %s 2>&1 | FileCheck %s
// RUN: %cpp-verify --diagnostics-format=json %s 2>/dev/null \
// RUN:   | FileCheck %s --check-prefix=JSON
//
// A proof that holds because no execution reaches the claim proves nothing,
// so every Verified result is checked for it. Assumptions enter a proof only
// through preconditions, behavior assumptions, type invariants, callee
// contracts, and trusted contracts; a verified callee always returns, so
// only the others can make the claims after them unreachable.

// The precondition can never hold.
int never(int x)
  cppverify::pre(x > 0 && x < 0)
  cppverify::post(cppverify::result == 42)
{
  return 0;
}
// CHECK-DAG: Verified: never [backend=z3] [vacuous]
// CHECK-DAG: warning: never: the precondition is unsatisfiable, so every claim about it holds vacuously
// JSON-DAG: "function":"never"{{.*}}"status":"verified","vacuous":true

// A trusted contract that no call can satisfy, on every path.
[[cppverify::trusted]] int impossible(int x)
  cppverify::post(cppverify::result > x && cppverify::result < x);

int always_calls(int x)
  cppverify::post(cppverify::result == 7)
{
  return impossible(x);
}
// CHECK-DAG: Verified: always_calls [backend=z3] [vacuous] [trusts=impossible]
// CHECK-DAG: warning: always_calls: no execution reaches the end, so its postcondition holds vacuously; check the contracts it calls and its assumptions

// The same contract on one path: the rest of the function is checked, the
// call's path is reported.
int sometimes_calls(int x)
  cppverify::pre(x >= 0 && x <= 10)
  cppverify::post(cppverify::result >= 0)
{
  if (x == 3) {
    int y = impossible(x);
    return -1;
  }
  return x;
}
// CHECK-DAG: Verified: sometimes_calls [backend=z3] [vacuous] [trusts=impossible]
// CHECK-DAG: vacuity.cpp:[[@LINE-6]]:5: warning: sometimes_calls: the trusted contract of impossible contradicts the state of this call, so everything after it holds vacuously

// A behavior whose assumption contradicts the preconditions is never checked.
int clipped(int x)
  cppverify::pre(x >= 0 && x <= 10)
  cppverify::behavior(small, x < 5)
    cppverify::post(cppverify::result == x)
  cppverify::behavior(huge, x > 20)
    cppverify::post(cppverify::result == 1000)
  cppverify::behavior(large, x >= 5)
    cppverify::post(cppverify::result == x)
  cppverify::complete_behaviors
{
  return x;
}
// CHECK-DAG: Verified: clipped [backend=z3]
// CHECK-DAG: vacuity.cpp:[[@LINE-9]]:31: warning: clipped: behavior huge never applies: its assumption contradicts the preconditions, so its postconditions are never checked

// A type invariant that can never hold is a precondition that cannot hold.
struct span { int lo; int hi; cppverify::type_invariant(lo <= hi && hi < lo); };

int width(span s)
  cppverify::post(cppverify::result >= 0)
{
  return s.hi - s.lo;
}
// CHECK-DAG: Verified: width [backend=z3] [vacuous]
// CHECK-DAG: warning: width: the precondition is unsatisfiable, so every claim about it holds vacuously

// Not flagged: a defensive branch the precondition excludes. Code may be
// unreachable for good reasons; only assumptions that kill the claims are.
int defensive(const int *p)
  cppverify::pre(p != nullptr)
  cppverify::post(cppverify::result == 1)
{
  if (p == nullptr)
    return -1;
  return 1;
}
// CHECK-DAG: Verified: defensive [backend=z3]{{$}}

// Not flagged: a trusted contract that some calls can satisfy. The proof
// rests on it, which [trusts=...] says.
[[cppverify::trusted]] int positive_only(int x)
  cppverify::post(cppverify::result == x && x > 0);

int partly(int x)
  cppverify::pre(x >= -5 && x <= 10)
  cppverify::post(cppverify::result >= -5)
{
  return positive_only(x - 6);
}
// CHECK-DAG: Verified: partly [backend=z3] [trusts=positive_only]{{$}}
