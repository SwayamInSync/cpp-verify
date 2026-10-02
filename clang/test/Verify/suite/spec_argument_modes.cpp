// RUN: not %cpp-verify %s 2>&1 | FileCheck %s
//
// An argument of a spec is a mathematical integer, whatever the spec
// returns: a + 1 below is 2147483648 and does not wrap.

spec bool above(int x, int n)
  decreases(n < 0 ? 0 : n)
{
  return n <= 0 ? x > 2147483647 : above(x, n - 1);
}

proof void above_holds(int a)
  pre(a == 2147483647)
  post(above(a + 1, 1))
{
  ghost { reveal_with_fuel(above, 3); }
}
// CHECK-DAG: Verified: above_holds

proof void above_fails(int a)
  pre(a == 2147483647)
  post(!above(a + 1, 1))
{
  ghost { reveal_with_fuel(above, 3); }
}
// CHECK-DAG: error: verification failed: above_fails {{.*}}(counterexample: a {{.*}}= 2147483647) [backend=z3] [reason=counterexample]
