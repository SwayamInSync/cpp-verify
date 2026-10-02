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
  pre(x > 0 && x < 0)
  post(result == 42)
{
  return 0;
}
// CHECK-DAG: Verified: never [backend=z3] [vacuous]
// CHECK-DAG: warning: never: the precondition is unsatisfiable, so every claim about it holds vacuously
// JSON-DAG: "function":"never"{{.*}}"status":"verified","vacuous":true

// A trusted contract that no call can satisfy, on every path.
[[cppverify::trusted]] int impossible(int x)
  post(result > x && result < x);

int always_calls(int x)
  post(result == 7)
{
  return impossible(x);
}
// CHECK-DAG: Verified: always_calls [backend=z3] [vacuous] [trusts=impossible]
// CHECK-DAG: warning: always_calls: no execution reaches the end, so its postcondition holds vacuously; check the contracts it calls and its assumptions

// The same contract on one path: the rest of the function is checked, the
// call's path is reported.
int sometimes_calls(int x)
  pre(x >= 0 && x <= 10)
  post(result >= 0)
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
  pre(x >= 0 && x <= 10)
  behavior(small, x < 5)
    post(result == x)
  behavior(huge, x > 20)
    post(result == 1000)
  behavior(large, x >= 5)
    post(result == x)
  complete_behaviors
{
  return x;
}
// CHECK-DAG: Verified: clipped [backend=z3]
// CHECK-DAG: vacuity.cpp:[[@LINE-9]]:20: warning: clipped: behavior huge never applies: its assumption contradicts the preconditions, so its postconditions are never checked

// A type invariant that can never hold is a precondition that cannot hold.
struct span { int lo; int hi; type_invariant(lo <= hi && hi < lo); };

int width(span s)
  post(result >= 0)
{
  return s.hi - s.lo;
}
// CHECK-DAG: Verified: width [backend=z3] [vacuous]
// CHECK-DAG: warning: width: the precondition is unsatisfiable, so every claim about it holds vacuously

// Not flagged: a defensive branch the precondition excludes. Code may be
// unreachable for good reasons; only assumptions that kill the claims are.
int defensive(const int *p)
  pre(p != nullptr)
  post(result == 1)
{
  if (p == nullptr)
    return -1;
  return 1;
}
// CHECK-DAG: Verified: defensive [backend=z3]{{$}}

// Not flagged: a trusted contract that some calls can satisfy. The proof
// rests on it, which [trusts=...] says.
[[cppverify::trusted]] int positive_only(int x)
  post(result == x && x > 0);

int partly(int x)
  pre(x >= -5 && x <= 10)
  post(result >= -5)
{
  return positive_only(x - 6);
}
// CHECK-DAG: Verified: partly [backend=z3] [trusts=positive_only]{{$}}
