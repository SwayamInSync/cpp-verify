// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

spec int terminating_countdown(int n)
  decreases(n)
{
  if (n > 0) {
    int next = n - 1;
    return terminating_countdown(next);
  }
  return 0;
}

spec int nonterminating_descent(int n)
  decreases(n)
{
  return nonterminating_descent(n - 1);
}

spec int terminating_after_branch(int n)
  decreases(n)
{
  int next;
  if (n > 0)
    next = n - 1;
  else
    return 0;
  return terminating_after_branch(next);
}

spec int nonterminating_after_branch(int n)
  decreases(n * n)
{
  int next;
  if (n > 0)
    next = n;
  else
    next = n;
  return 1 + nonterminating_after_branch(next);
}

proof void nonterminating_proof(int n)
  decreases(n)
{
  nonterminating_proof(n - 1);
}

// VERIFY-DAG: Verified: spec decreases: terminating_countdown
// VERIFY-DAG: Verified: spec decreases: terminating_after_branch
// VERIFY-DAG: error: spec decreases failed: nonterminating_descent
// VERIFY-DAG: error: spec decreases failed: nonterminating_after_branch
// VERIFY-DAG: error: decreases failed: nonterminating_proof
