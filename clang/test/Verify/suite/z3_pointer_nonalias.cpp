// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int valid_nonnull_default_nonalias(int *p, int *q)
  pre(p != nullptr && q != nullptr)
  post(result == 1)
{
  return p != q;
}

int invalid_nulls_excluded_by_nonalias(int *p, int *q)
  post(result == 1)
{
  if (p == nullptr && q == nullptr)
    return 0;
  return 1;
}

// VERIFY-DAG: Verified: valid_nonnull_default_nonalias
// VERIFY-DAG: error: verification failed: invalid_nulls_excluded_by_nonalias
