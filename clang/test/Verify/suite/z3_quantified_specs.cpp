// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: %cpp-verify --lower-only --timeout=1 %s -- 2>&1 | FileCheck %s --check-prefix=LOWER

cppverify::spec int bump(int x) {
  return x + 1;
}

cppverify::spec int countdown(int n)
  cppverify::decreases(n)
{
  if (n > 0)
    return countdown(n - 1);
  return 0;
}

cppverify::spec bool contains_last(int limit) {
  return cppverify::exists(j, 0, limit, j == limit - 1);
}

cppverify::spec bool binder_shadows_parameter(int j) {
  return cppverify::forall(j, 0, 1, j == 0);
}

cppverify::spec bool exists_below_ten(int target) {
  return cppverify::exists(k, 0, 10, k == target);
}

int valid_quantified_nonrecursive_spec(int n)
  cppverify::pre(n >= 0 && n <= 100)
  cppverify::post(cppverify::forall(k, 0, n, bump(k) == k + 1))
{
  return n;
}

int valid_nested_quantified_bound(int n)
  cppverify::pre(n >= 0 && n <= 100)
  cppverify::post(cppverify::forall(k, 0, n, contains_last(k + 1)))
{
  return n;
}

int valid_quantified_binder_shadowing(int n)
  cppverify::pre(n >= 0 && n <= 100)
  cppverify::post(cppverify::forall(k, 0, n, binder_shadows_parameter(k + 10)))
{
  return n;
}

cppverify::proof void valid_quantified_recursive_spec()
  cppverify::post(cppverify::forall(k, 0, 4, countdown(k) == 0))
{
  cppverify::reveal_with_fuel(countdown, 4);
}

int invalid_quantified_spec(int n)
  cppverify::pre(n > 0)
  cppverify::post(cppverify::forall(k, 0, n, bump(k) == k + 2))
{
  return n;
}

int invalid_quantifier_capture(int n)
  cppverify::pre(n == 100)
  cppverify::post(cppverify::forall(k, 5, 100, exists_below_ten(k)))
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

// LOWER-DAG: Lowered: spec decreases: countdown
// LOWER-DAG: Lowered: valid_quantified_nonrecursive_spec
// LOWER-DAG: Lowered: valid_nested_quantified_bound
// LOWER-DAG: Lowered: valid_quantified_binder_shadowing
// LOWER-DAG: Lowered: valid_quantified_recursive_spec
// LOWER-DAG: Lowered: invalid_quantified_spec
// LOWER-DAG: Lowered: invalid_quantifier_capture
// LOWER-NOT: Verified:
// LOWER-NOT: error:
// LOWER-NOT: Unresolved:
