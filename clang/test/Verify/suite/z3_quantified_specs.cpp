// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

spec int bump(int x) {
  return x + 1;
}

spec int countdown(int n)
  decreases(n)
{
  if (n > 0)
    return countdown(n - 1);
  return 0;
}

spec bool contains_last(int limit) {
  return exists(j, 0, limit, j == limit - 1);
}

spec bool binder_shadows_parameter(int j) {
  return forall(j, 0, 1, j == 0);
}

spec bool exists_below_ten(int target) {
  return exists(k, 0, 10, k == target);
}

int valid_quantified_nonrecursive_spec(int n)
  pre(n >= 0 && n <= 100)
  post(forall(k, 0, n, bump(k) == k + 1))
{
  return n;
}

int valid_nested_quantified_bound(int n)
  pre(n >= 0 && n <= 100)
  post(forall(k, 0, n, contains_last(k + 1)))
{
  return n;
}

int valid_quantified_binder_shadowing(int n)
  pre(n >= 0 && n <= 100)
  post(forall(k, 0, n, binder_shadows_parameter(k + 10)))
{
  return n;
}

proof void valid_quantified_recursive_spec()
  post(forall(k, 0, 4, countdown(k) == 0))
{
  reveal_with_fuel(countdown, 4);
}

int invalid_quantified_spec(int n)
  pre(n > 0)
  post(forall(k, 0, n, bump(k) == k + 2))
{
  return n;
}

int invalid_quantifier_capture(int n)
  pre(n == 100)
  post(forall(k, 5, 100, exists_below_ten(k)))
{
  return n;
}

// VERIFY-DAG: spec axiom: bump
// VERIFY-DAG: spec decreases: countdown
// VERIFY-DAG: spec axiom: contains_last
// VERIFY-DAG: spec axiom: binder_shadows_parameter
// VERIFY-DAG: spec axiom: exists_below_ten
// VERIFY-DAG: Verified: valid_quantified_nonrecursive_spec
// VERIFY-DAG: Verified: valid_nested_quantified_bound
// VERIFY-DAG: Verified: valid_quantified_binder_shadowing
// VERIFY-DAG: Verified: valid_quantified_recursive_spec
// VERIFY-DAG: error: verification failed: invalid_quantified_spec
// VERIFY-DAG: error: verification failed: invalid_quantifier_capture
