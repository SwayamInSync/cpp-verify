// RUN: not %cpp-verify %s 2>&1 | FileCheck %s
// RUN: not %cpp-verify --backend=bmc --unroll=1 %s 2>&1 | FileCheck %s
//
// What recursive specs settle without a lemma, what needs one, and what the
// verifier says when one is needed.

spec int sum(int n)
  decreases(n)
{
  return n <= 0 ? 0 : n + sum(n - 1);
}

spec int fib(int n)
  decreases(n)
{
  return n <= 1 ? (n <= 0 ? 0 : 1) : fib(n - 1) + fib(n - 2);
}

// Applications at closed arguments are computed from definition instances,
// thousands of unfoldings deep.
void computed()
{
  ghost {
    contract_assert(sum(5000) == 12502500);
    contract_assert(fib(90) == 2880067194370816120);
  }
}

void computed_wrong()
{
  ghost { contract_assert(sum(5000) == 12502501); }
}

// A bounded domain is covered by evaluating the definitions across it.
void bounded(int n)
  pre(n >= 0 && n <= 200)
{
  ghost { contract_assert(2 * sum(n) == n * (n + 1)); }
}

void bounded_wrong(int n)
  pre(n >= 0 && n <= 200)
{
  ghost { contract_assert(2 * sum(n) == n * (n + 1) + (n == 137 ? 1 : 0)); }
}

// Unbounded, this is an induction: no finite unfolding settles it, so the
// verifier proves it by strong induction on n.
void inductive(int n)
  pre(n >= 0 && n <= 40000)
{
  ghost { contract_assert(2 * sum(n) == n * (n + 1)); }
}

// The recursion changes the accumulator, so the hypothesis at a fixed
// accumulator does not apply: this needs a lemma over every accumulator.
spec int accumulate(int n, int acc)
  decreases(n)
{
  return n <= 0 ? acc : accumulate(n - 1, acc + n);
}

void accumulated(int n)
  pre(n >= 0 && n <= 25000)
{
  ghost { contract_assert(accumulate(n, 0) == sum(n)); }
}

// The lemma's recursive call is the hypothesis at another accumulator.
proof void accumulate_sum(int n, int acc)
  pre(n >= 0 && n <= 25000 && acc >= 0 && acc <= 1000000000 - 40000 * n)
  post(accumulate(n, acc) == acc + sum(n))
  decreases(n)
{
  if (n > 0)
    accumulate_sum(n - 1, acc + n);
}

void accumulated_by_lemma(int n)
  pre(n >= 0 && n <= 25000)
{
  ghost {
    accumulate_sum(n, 0);
    contract_assert(accumulate(n, 0) == sum(n));
  }
}

// The induction as a lemma, stated in machine arithmetic.
proof void sum_closed(int n)
  pre(n >= 0 && n <= 40000)
  post(2 * sum(n) == n * (n + 1))
  decreases(n)
{
  if (n > 0)
    sum_closed(n - 1);
}

int gauss(int n)
  pre(n >= 0 && n <= 40000)
  post(result == sum(n))
{
  ghost { sum_closed(n); }
  return n * (n + 1) / 2;
}

// A proved assertion is a fact for what follows.
void steps(int n)
  pre(n >= 0 && n <= 40000)
{
  ghost {
    sum_closed(n);
    contract_assert(sum(n) <= 800020000);
    contract_assert(sum(n) - 800020000 <= 0);
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

