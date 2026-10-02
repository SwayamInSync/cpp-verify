// RUN: not %cpp-verify --timeout=20000 %s 2>&1 | FileCheck %s
//
// choose(k, body) is an integer for which body holds, when one exists, and
// otherwise an unspecified integer; choose(k, lo, hi, body) chooses in
// [lo, hi). Each choose is a function of the values its body mentions, so
// it is the same for the same values. A claim that holds for only some
// choices fails with a certified counterexample for another.

spec bool valid(const int *p, int n) { return true; }

spec int half(int n) { return choose(k, 2 * k == n); }

void even(int n)
  pre(n % 2 == 0 && n >= 0 && n <= 1000)
{
  contract_assert(2 * half(n) == n);
}
// CHECK-DAG: Verified: even

spec int index_of(const int *a, int n, int x)
{
  return choose(k, 0, n, a[k] == x);
}

void found(const int *a, int n, int x)
  pre(valid(a, n) && n >= 1 && n <= 1000)
  pre(exists(k, 0, n, a[k] == x))
{
  contract_assert(0 <= index_of(a, n, x) && index_of(a, n, x) < n);
  contract_assert(a[index_of(a, n, x)] == x);
}
// CHECK-DAG: Verified: found

spec int pick() { return choose(x, x > 0); }

void same_choice()
{
  contract_assert(pick() == pick());
  contract_assert(pick() > 0);
}
// CHECK-DAG: Verified: same_choice

void claims_one()
  post(pick() == 1)
{
}
// CHECK-DAG: error: verification failed: claims_one [{{.*}}::postcondition@{{.*}}[reason=counterexample]

void no_witness()
{
  contract_assert(choose(x, x * x == 2) == 0);
}
// CHECK-DAG: error: verification failed: no_witness [{{.*}}::assertion@{{.*}}[reason=counterexample]

// In ghost code a choice is stored like any mathematical value: the store
// must fit, which the range guarantees when a witness exists.
void ghost_choice(int n)
  pre(n >= 1 && n <= 100)
{
  ghost int w = choose(k, 0, n + 1, k == n);
  contract_assert(w == n);
}
// CHECK-DAG: Verified: ghost_choice
