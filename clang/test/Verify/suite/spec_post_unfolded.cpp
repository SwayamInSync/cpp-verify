// RUN: not %cpp-verify --timeout=10000 %s 2>&1 | FileCheck %s
// RUN: %cpp-verify --lower-only --dump-ir=4 %s 2>&1 | FileCheck %s --check-prefix=DUMP
//
// A spec's proved postcondition holds at every application the solver sees,
// as Dafny's function postconditions do: those the function names, and those
// inside the definitions it receives, as deep as the fuel unfolds them.

#include <cppverify.h>

spec int fibo(int n)
  decreases(n)
  post(result >= 0)
{
  if (n <= 0) return 0;
  if (n == 1) return 1;
  return fibo(n - 2) + fibo(n - 1);
}

// fibo(j - 1) <= fibo(j) needs fibo(j - 2) >= 0, an application that only
// the unfolding of fibo(j) names.
proof void fibo_monotone(int i, int j)
  pre(i <= j)
  post(fibo(i) <= fibo(j))
  decreases(j - i)
{
  if (i < j)
    fibo_monotone(i, j - 1);
}
// CHECK-DAG: Verified: fibo_monotone
// DUMP: (>= (spec${{[^ ]+}} (- j_0 2)) 0)

// The facts are theorems, so a false claim still fails with a certified
// counterexample: fibo(-2) == fibo(-1) == 0.
proof void fibo_strict(int i, int j)
  pre(i < j)
  post(fibo(i) < fibo(j))
  decreases(j - i)
{
  if (i < j - 1)
    fibo_strict(i, j - 1);
}
// CHECK-DAG: error: verification failed: fibo_strict {{.*}}[reason=counterexample]

// With more fuel the deeper applications get them too.
void deeper(int n)
  pre(n >= 3)
{
  ghost { reveal_with_fuel(fibo, 3); }
  contract_assert(fibo(n) >= fibo(n - 2));
}
// CHECK-DAG: Verified: deeper

// A hidden spec gives no definition, so nothing inside one.
proof void hidden_monotone(int j)
  post(fibo(j - 1) <= fibo(j))
{
  ghost { hide(fibo); }
}
// CHECK-DAG: Unresolved: hidden_monotone {{.*}}[reason=spec.hidden]

// A spec's own post check sees them too: fibo(n) - fibo(n - 1) is
// fibo(n - 2) where n >= 2.
spec int gap(int n)
  post(result >= 0)
{
  return fibo(n) - fibo(n - 1);
}
// CHECK-DAG: Verified: spec post: gap

spec int gap_rec(int n)
  decreases(n)
  post(result >= 0)
{
  return n <= 0 ? 0 : gap_rec(n - 1) + fibo(n) - fibo(n - 1);
}
// CHECK-DAG: Verified: spec decreases and post: gap_rec

// fibo(0) - fibo(-1) is 0.
spec int gap_positive(int n)
  post(result > 0)
{
  return fibo(n) - fibo(n - 1);
}
// CHECK-DAG: error: spec post failed: gap_positive {{.*}}[reason=counterexample]
