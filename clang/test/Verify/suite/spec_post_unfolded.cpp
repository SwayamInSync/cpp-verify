// RUN: not %cpp-verify --timeout=10000 %s -- 2>&1 | FileCheck %s
// RUN: %cpp-verify --lower-only --dump-ir=4 %s -- 2>&1 | FileCheck %s --check-prefix=DUMP
//
// A spec's proved postcondition holds at every application the solver sees,
// as Dafny's function postconditions do: those the function names, and those
// inside the definitions it receives, as deep as the fuel unfolds them.

#include <cppverify.h>

cppverify::spec int fibo(int n)
  cppverify::decreases(n)
  cppverify::post(cppverify::result >= 0)
{
  if (n <= 0) return 0;
  if (n == 1) return 1;
  return fibo(n - 2) + fibo(n - 1);
}

// fibo(j - 1) <= fibo(j) needs fibo(j - 2) >= 0, an application that only
// the unfolding of fibo(j) names.
cppverify::proof void fibo_monotone(int i, int j)
  cppverify::pre(i <= j)
  cppverify::post(fibo(i) <= fibo(j))
  cppverify::decreases(j - i)
{
  if (i < j)
    fibo_monotone(i, j - 1);
}
// CHECK-DAG: Verified: fibo_monotone
// DUMP: (>= (spec${{[^ ]+}} (- j_0 2)) 0)

// The facts are theorems, so a false claim still fails with a certified
// counterexample: fibo(-2) == fibo(-1) == 0.
cppverify::proof void fibo_strict(int i, int j)
  cppverify::pre(i < j)
  cppverify::post(fibo(i) < fibo(j))
  cppverify::decreases(j - i)
{
  if (i < j - 1)
    fibo_strict(i, j - 1);
}
// CHECK-DAG: error: verification failed: fibo_strict {{.*}}[reason=counterexample]

// With more fuel the deeper applications get them too.
void deeper(int n)
  cppverify::pre(n >= 3)
{
  cppverify::ghost { cppverify::reveal_with_fuel(fibo, 3); }
  cppverify::check(fibo(n) >= fibo(n - 2));
}
// CHECK-DAG: Verified: deeper

// A hidden spec gives no definition, so nothing inside one.
cppverify::proof void hidden_monotone(int j)
  cppverify::post(fibo(j - 1) <= fibo(j))
{
  cppverify::ghost { cppverify::hide(fibo); }
}
// CHECK-DAG: Unresolved: hidden_monotone {{.*}}[reason=spec.hidden]

// A spec's own post check sees them too: fibo(n) - fibo(n - 1) is
// fibo(n - 2) where n >= 2.
cppverify::spec int gap(int n)
  cppverify::post(cppverify::result >= 0)
{
  return fibo(n) - fibo(n - 1);
}
// CHECK-DAG: Verified: spec post: gap

cppverify::spec int gap_rec(int n)
  cppverify::decreases(n)
  cppverify::post(cppverify::result >= 0)
{
  return n <= 0 ? 0 : gap_rec(n - 1) + fibo(n) - fibo(n - 1);
}
// CHECK-DAG: Verified: spec decreases and post: gap_rec

// fibo(0) - fibo(-1) is 0.
cppverify::spec int gap_positive(int n)
  cppverify::post(cppverify::result > 0)
{
  return fibo(n) - fibo(n - 1);
}
// CHECK-DAG: error: spec post failed: gap_positive {{.*}}[reason=counterexample]
