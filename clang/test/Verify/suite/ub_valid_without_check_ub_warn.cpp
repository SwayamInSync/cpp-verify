// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify --no-check-ub --timeout=30000 %s -- 2>&1 | FileCheck %s --check-prefix=WARN
// RUN: %cpp-verify --timeout=30000 %s -- 2>&1 | FileCheck %s --check-prefix=OK
//
// valid(p, n) is only meaningful with memory checking, the default. Under
// --no-check-ub the marker's deliberately trivial spec body folds to `true`,
// the declared extent never becomes an assumption, and heap facts do not
// survive from the precondition into the postcondition -- so the solver
// reports a counterexample for a function that is plainly correct.
//
// The identity below is P |- P with an empty body. It cannot legitimately fail.
// Under --no-check-ub it does, so the driver warns rather than letting a
// fabricated counterexample stand unexplained. By default it verifies.

cppverify::spec bool valid(int* p, int n) { return true; }

int echo_point(int* a)
  cppverify::pre(valid(a, 3) && a[0] > 0)
  cppverify::post(a[0] > 0)
{
  return 0;
}

// WARN: warning: contract of echo_point uses the valid(p, n) extent marker
// WARN-SAME: memory checking is disabled (--no-check-ub)
// OK: Verified: echo_point
