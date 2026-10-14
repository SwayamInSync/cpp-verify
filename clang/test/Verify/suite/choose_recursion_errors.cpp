// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s
//
// A choose belongs to the function it is written in: a spec that applies
// itself inside one is recursive and needs a measure, and an inductive
// predicate may not apply its group inside one, where it is not positive.

// f(7) would have to equal f(7) + 1.
cppverify::spec int f(int n)
{
  return cppverify::choose(k, n == 7 ? k == f(n) + 1 : k == 0);
}
// CHECK-DAG: error: f: recursive spec and proof functions require decreases

int forty_two(int x)
  cppverify::post(cppverify::result == 42)
{
  cppverify::check(f(x) == f(x));
  if (x == 7)
    return 0;
  return 42;
}

cppverify::spec int ping(int n);
cppverify::spec int pong(int n) { return cppverify::choose(k, k == ping(n)); }
cppverify::spec int ping(int n) { return n <= 0 ? 0 : pong(n) + 1; }
// CHECK-DAG: error: {{ping|pong}}: mutually recursive spec functions require decreases clauses, all of the same length

cppverify::spec bool liar(int n)
  cppverify::inductive
{
  return cppverify::choose(k, 0, 2, k == (liar(n) ? 0 : 1)) == 1;
}
// CHECK-DAG: error: liar: an inductive predicate occurs in the bodies of its group only positively, never inside cppverify::choose
// CHECK-NOT: Verified
