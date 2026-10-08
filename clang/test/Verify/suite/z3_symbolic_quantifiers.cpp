// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int valid_forall(int n)
  cppverify::pre(n >= 0)
  cppverify::post(cppverify::forall(k, 0, n, k >= 0 && k < n))
{
  return n;
}

int valid_exists(int n)
  cppverify::pre(n > 0)
  cppverify::post(cppverify::exists(k, 0, n, k == 0))
{
  return n;
}

int invalid_forall(int n)
  cppverify::pre(n > 0)
  cppverify::post(cppverify::forall(k, 0, n, k < 0))
{
  return n;
}

int invalid_empty_exists()
  cppverify::post(cppverify::exists(k, 0, 0, k == k))
{
  return 0;
}

long valid_wide_quantifier_bounds(long n)
  cppverify::pre(n >= 0 && n <= 100)
  cppverify::post(cppverify::forall(i, 0L, n, i >= 0 && i < n))
{
  return n;
}

cppverify::proof void valid_wide_quantifier_proof(long n)
  cppverify::pre(n >= 0 && n <= 100)
  cppverify::post(cppverify::forall(i, 0, n, i >= 0 && i < n))
{
}

long invalid_wide_quantifier(long n)
  cppverify::pre(n > 0)
  cppverify::post(cppverify::forall(i, 0, n, i < 0))
{
  return n;
}

// VERIFY-DAG: Verified: valid_forall
// VERIFY-DAG: Verified: valid_exists
// VERIFY-DAG: error: verification failed: invalid_forall
// VERIFY-DAG: error: verification failed: invalid_empty_exists
// VERIFY-DAG: Verified: valid_wide_quantifier_bounds
// VERIFY-DAG: Verified: valid_wide_quantifier_proof
// VERIFY-DAG: error: verification failed: invalid_wide_quantifier
