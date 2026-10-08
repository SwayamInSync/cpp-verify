// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s
// RUN: not %cpp-verify --backend=bmc --unroll=1 %s -- 2>&1 | FileCheck %s
//
// What recursive specs settle without a lemma, what needs one, and what the
// verifier says when one is needed.

cppverify::spec int sum(int n)
  cppverify::decreases(n)
{
  return n <= 0 ? 0 : n + sum(n - 1);
}

cppverify::spec int fib(int n)
  cppverify::decreases(n)
{
  return n <= 1 ? (n <= 0 ? 0 : 1) : fib(n - 1) + fib(n - 2);
}

// Applications at closed arguments are computed from definition instances,
// thousands of unfoldings deep.
void computed()
{
  cppverify::ghost {
    cppverify::check(sum(5000) == 12502500);
    cppverify::check(fib(90) == 2880067194370816120);
  }
}

void computed_wrong()
{
  cppverify::ghost { cppverify::check(sum(5000) == 12502501); }
}

// A bounded domain is covered by evaluating the definitions across it.
void bounded(int n)
  cppverify::pre(n >= 0 && n <= 200)
{
  cppverify::ghost { cppverify::check(2 * sum(n) == n * (n + 1)); }
}

void bounded_wrong(int n)
  cppverify::pre(n >= 0 && n <= 200)
{
  cppverify::ghost { cppverify::check(2 * sum(n) == n * (n + 1) + (n == 137 ? 1 : 0)); }
}

// Unbounded, this is an induction: no finite unfolding settles it, so the
// verifier proves it by strong induction on n.
void inductive(int n)
  cppverify::pre(n >= 0 && n <= 40000)
{
  cppverify::ghost { cppverify::check(2 * sum(n) == n * (n + 1)); }
}

// The recursion changes the accumulator, so the hypothesis at a fixed
// accumulator does not apply: this needs a lemma over every accumulator.
cppverify::spec int accumulate(int n, int acc)
  cppverify::decreases(n)
{
  return n <= 0 ? acc : accumulate(n - 1, acc + n);
}

void accumulated(int n)
  cppverify::pre(n >= 0 && n <= 25000)
{
  cppverify::ghost { cppverify::check(accumulate(n, 0) == sum(n)); }
}

// The lemma's recursive call is the hypothesis at another accumulator.
cppverify::proof void accumulate_sum(int n, int acc)
  cppverify::pre(n >= 0 && n <= 25000 && acc >= 0 && acc <= 1000000000 - 40000 * n)
  cppverify::post(accumulate(n, acc) == acc + sum(n))
  cppverify::decreases(n)
{
  if (n > 0)
    accumulate_sum(n - 1, acc + n);
}

void accumulated_by_lemma(int n)
  cppverify::pre(n >= 0 && n <= 25000)
{
  cppverify::ghost {
    accumulate_sum(n, 0);
    cppverify::check(accumulate(n, 0) == sum(n));
  }
}

// The induction as a lemma, stated in machine arithmetic.
cppverify::proof void sum_closed(int n)
  cppverify::pre(n >= 0 && n <= 40000)
  cppverify::post(2 * sum(n) == n * (n + 1))
  cppverify::decreases(n)
{
  if (n > 0)
    sum_closed(n - 1);
}

int gauss(int n)
  cppverify::pre(n >= 0 && n <= 40000)
  cppverify::post(cppverify::result == sum(n))
{
  cppverify::ghost { sum_closed(n); }
  return n * (n + 1) / 2;
}

// A proved assertion is a fact for what follows.
void steps(int n)
  cppverify::pre(n >= 0 && n <= 40000)
{
  cppverify::ghost {
    sum_closed(n);
    cppverify::check(sum(n) <= 800020000);
    cppverify::check(sum(n) - 800020000 <= 0);
  }
}

// CHECK-DAG: Verified: computed
// CHECK-DAG: verification failed: computed_wrong [{{.*}}::assertion@
// CHECK-DAG: Verified: bounded [backend=
// CHECK-DAG: verification failed: bounded_wrong {{.*}}n [ssa=n_0] [type=i32] = 137
// CHECK-DAG: Verified: inductive
// CHECK-DAG: Unresolved: accumulated [backend={{z3|bmc, bound=0}}] [reason=spec.fuel] {{.*}}by induction in a proof function
// CHECK-DAG: Verified: accumulate_sum
// CHECK-DAG: Verified: accumulated_by_lemma
// CHECK-DAG: Verified: sum_closed
// CHECK-DAG: Verified: gauss
// CHECK-DAG: Verified: steps

