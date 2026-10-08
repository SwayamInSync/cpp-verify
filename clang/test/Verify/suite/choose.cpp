// RUN: not %cpp-verify --timeout=20000 %s 2>&1 | FileCheck %s
//
// choose(k, body) is an integer for which body holds, when one exists, and
// otherwise an unspecified integer; choose(k, lo, hi, body) chooses in
// [lo, hi). Each choose is a function of the values its body mentions, so
// it is the same for the same values. A claim that holds for only some
// choices fails with a certified counterexample for another.

cppverify::spec bool valid(const int *p, int n) { return true; }

cppverify::spec int half(int n) { return cppverify::choose(k, 2 * k == n); }

void even(int n)
  cppverify::pre(n % 2 == 0 && n >= 0 && n <= 1000)
{
  cppverify::check(2 * half(n) == n);
}
// CHECK-DAG: Verified: even

cppverify::spec int index_of(const int *a, int n, int x)
{
  return cppverify::choose(k, 0, n, a[k] == x);
}

void found(const int *a, int n, int x)
  cppverify::pre(valid(a, n) && n >= 1 && n <= 1000)
  cppverify::pre(cppverify::exists(k, 0, n, a[k] == x))
{
  cppverify::check(0 <= index_of(a, n, x) && index_of(a, n, x) < n);
  cppverify::check(a[index_of(a, n, x)] == x);
}
// CHECK-DAG: Verified: found

cppverify::spec int pick() { return cppverify::choose(x, x > 0); }

void same_choice()
{
  cppverify::check(pick() == pick());
  cppverify::check(pick() > 0);
}
// CHECK-DAG: Verified: same_choice

void claims_one()
  cppverify::post(pick() == 1)
{
}
// CHECK-DAG: error: verification failed: claims_one [{{.*}}::postcondition@{{.*}}[reason=counterexample]

void no_witness()
{
  cppverify::check(cppverify::choose(x, x * x == 2) == 0);
}
// CHECK-DAG: error: verification failed: no_witness [{{.*}}::assertion@{{.*}}[reason=counterexample]

// In ghost code a choice is stored like any mathematical value: the store
// must fit, which the range guarantees when a witness exists.
void ghost_choice(int n)
  cppverify::pre(n >= 1 && n <= 100)
{
  cppverify::ghost int w = cppverify::choose(k, 0, n + 1, k == n);
  cppverify::check(w == n);
}
// CHECK-DAG: Verified: ghost_choice
