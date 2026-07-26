// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int valid_early_return(int x)
  post((x > 0 && result == 1) || (x <= 0 && result == 0))
{
  if (x > 0)
    return 1;
  contract_assert(x <= 0);
  return 0;
}

int invalid_early_return(int x)
  post(result == 0)
{
  if (x > 0)
    return 1;
  return 0;
}

// VERIFY-DAG: Verified: valid_early_return
// VERIFY-DAG: error: verification failed: invalid_early_return
