// RUN: not %cpp-verify --timeout=60000 %s -- 2>&1 | FileCheck %s
//
// An induction through another member of a recursion group: even reaches
// even(n - 2) through odd. Its proof takes about 3 s of solving, so the
// timeout leaves each induction attempt (a sixth of it) room.

#include <cppverify.h>

cppverify::spec bool odd(int n);
cppverify::spec bool even(int n) cppverify::decreases(n) { return n <= 0 ? true : odd(n - 1); }
cppverify::spec bool odd(int n) cppverify::decreases(n) { return n <= 0 ? false : even(n - 1); }

cppverify::proof void even_mod(int n)
  cppverify::pre(n >= 0)
  cppverify::post(even(n) == (n % 2 == 0))
{
}
// CHECK-DAG: Verified: even_mod [backend=z3] [by induction following even]

// A false claim still fails, with a counterexample checked against the
// definitions: odd(1) holds.
cppverify::proof void even_wrong(int n)
  cppverify::pre(n >= 0)
  cppverify::post(even(n) == (n % 2 == 1))
{
}
// CHECK-DAG: error: verification failed: even_wrong {{.*}}[reason=counterexample]
