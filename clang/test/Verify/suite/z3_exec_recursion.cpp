// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int valid_countdown(int n)
  pre(n >= 0)
  post(result == 0)
  decreases(n)
{
  if (n == 0)
    return 0;
  return valid_countdown(n - 1);
}

int invalid_nonterminating_exec(int n)
  pre(n >= 0)
  post(result == 0)
  post(result == 1)
  decreases(n)
{
  return invalid_nonterminating_exec(n);
}

// VERIFY-DAG: Verified: valid_countdown
// VERIFY-DAG: error: decreases failed: invalid_nonterminating_exec
