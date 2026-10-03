// REQUIRES: cvc5
// RUN: not %cpp-verify --backend=race --jobs=4 --timeout=10000 %s 2>&1 \
// RUN:   | FileCheck %s
// RUN: %cpp-verify --backend=race --lower-only %s 2>&1 \
// RUN:   | FileCheck %s --check-prefix=LOWER
// RUN: not %cpp-verify --obligation-out=%t.obligations %s > /dev/null 2>&1
// RUN: not %cpp-verify --backend=race --jobs=4 --timeout=10000 \
// RUN:   --obligation-in=%t.obligations 2>&1 \
// RUN:   | FileCheck %s --check-prefix=REPLAY
//
// Z3 and cvc5 run at once, as Frama-C's prover list: the first proof or
// certified counterexample stands and stops the other solver, and where
// neither settles a function the obligations each proved are joined. The
// tag names the solver that settled it.

#include <cppverify.h>
using cppverify::seq;

int add_one(int x)
  pre(x < 1000)
  post(result == x + 1)
{
  return x + 1;
}
// CHECK-DAG: Verified: add_one [backend={{z3|cvc5|z3\+cvc5}}]
// LOWER-DAG: Lowered: add_one
// LOWER-NOT: Verified:
// REPLAY-DAG: Verified: {{.*}}add_one{{.*}} [backend={{z3|cvc5|z3\+cvc5}}]

int wrong_bound(int x)
  pre(x >= 0 && x < 10)
  post(result < 10)
{
  return x + 1;
}
// CHECK-DAG: error: verification failed: wrong_bound {{.*}}[backend={{z3|cvc5}}] [reason=counterexample]
// REPLAY-DAG: wrong_bound {{.*}}[reason=counterexample]

proof void pushed(seq s, int x)
  post((s.push(x)).len() == s.len() + 1)
  post((s.push(x))[s.len()] == x)
{
}
// CHECK-DAG: Verified: pushed [backend={{z3|cvc5|z3\+cvc5}}]
