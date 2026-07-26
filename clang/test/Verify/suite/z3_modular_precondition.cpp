// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int witness_zero(int x)
  pre(x == 0)
  post(result == 0 && x == 0)
{
  return 0;
}

int valid_call(int x)
  pre(x == 0)
  post(result == 0)
{
  return witness_zero(x);
}

int invalid_call(int x)
  post(result == 0)
{
  return witness_zero(x);
}

// VERIFY-DAG: Verified: witness_zero
// VERIFY-DAG: Verified: valid_call
// VERIFY-DAG: error: verification failed: invalid_call
