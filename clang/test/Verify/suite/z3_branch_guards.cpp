// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY

int requires_positive(int x)
  cppverify::pre(x > 0)
  cppverify::post(cppverify::result == x)
{
  return x;
}

int valid_guarded_call(int x)
  cppverify::post(cppverify::result == x)
{
  if (x > 0)
    return requires_positive(x);
  return x;
}

int valid_guarded_assert(int x)
  cppverify::post(cppverify::result == x)
{
  if (x > 0)
    cppverify::check(x > 0);
  return x;
}

int invalid_guarded_call(int x)
  cppverify::pre(x <= 0)
  cppverify::post(cppverify::result == x)
{
  if (x <= 0)
    return requires_positive(x);
  return x;
}

// VERIFY-DAG: Verified: requires_positive
// VERIFY-DAG: Verified: valid_guarded_call
// VERIFY-DAG: Verified: valid_guarded_assert
// VERIFY-DAG: error: verification failed: invalid_guarded_call
