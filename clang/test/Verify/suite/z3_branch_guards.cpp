// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int requires_positive(int x)
  pre(x > 0)
  post(result == x)
{
  return x;
}

int valid_guarded_call(int x)
  post(result == x)
{
  if (x > 0)
    return requires_positive(x);
  return x;
}

int valid_guarded_assert(int x)
  post(result == x)
{
  if (x > 0)
    contract_assert(x > 0);
  return x;
}

int invalid_guarded_call(int x)
  pre(x <= 0)
  post(result == x)
{
  if (x <= 0)
    return requires_positive(x);
  return x;
}

// VERIFY-DAG: Verified: requires_positive
// VERIFY-DAG: Verified: valid_guarded_call
// VERIFY-DAG: Verified: valid_guarded_assert
// VERIFY-DAG: error: verification failed: invalid_guarded_call
