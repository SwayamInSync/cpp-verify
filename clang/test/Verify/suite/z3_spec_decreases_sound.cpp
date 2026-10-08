// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY

cppverify::spec int terminating_countdown(int n)
  cppverify::decreases(n)
{
  if (n > 0) {
    int next = n - 1;
    return terminating_countdown(next);
  }
  return 0;
}

cppverify::spec int nonterminating_descent(int n)
  cppverify::decreases(n)
{
  return nonterminating_descent(n - 1);
}

cppverify::spec int terminating_after_branch(int n)
  cppverify::decreases(n)
{
  int next;
  if (n > 0)
    next = n - 1;
  else
    return 0;
  return terminating_after_branch(next);
}

cppverify::spec int nonterminating_after_branch(int n)
  cppverify::decreases(n * n)
{
  int next;
  if (n > 0)
    next = n;
  else
    next = n;
  return 1 + nonterminating_after_branch(next);
}

cppverify::proof void nonterminating_proof(int n)
  cppverify::decreases(n)
{
  nonterminating_proof(n);
}

// VERIFY-DAG: Verified: spec decreases: terminating_countdown
// VERIFY-DAG: Verified: spec decreases: terminating_after_branch
// VERIFY-DAG: error: spec decreases failed: nonterminating_descent
// VERIFY-DAG: error: spec decreases failed: nonterminating_after_branch
// VERIFY-DAG: error: verification failed: nonterminating_proof [{{.*}}::termination@
