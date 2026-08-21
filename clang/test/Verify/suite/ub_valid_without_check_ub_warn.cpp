// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify --timeout=30000 %s 2>&1 | FileCheck %s --check-prefix=WARN
// RUN: %cpp-verify --check-ub --timeout=30000 %s 2>&1 | FileCheck %s --check-prefix=OK
//
// valid(p, n) is only meaningful under --check-ub. Without the flag the
// marker's deliberately trivial spec body folds to `true`, the declared extent
// never becomes an assumption, and heap facts do not survive from the
// precondition into the postcondition -- so the solver reports a counterexample
// for a function that is plainly correct.
//
// The identity below is P |- P with an empty body. It cannot legitimately fail.
// Without --check-ub it does, so the driver warns rather than letting a
// fabricated counterexample stand unexplained. With --check-ub it verifies.

spec bool valid(int* p, int n) { return true; }

int echo_point(int* a)
  pre(valid(a, 3) && a[0] > 0)
  post(a[0] > 0)
{
  return 0;
}

// WARN: warning: contract of echo_point uses the valid(p, n) extent marker
// WARN-SAME: --check-ub is not enabled
// OK: Verified: echo_point
