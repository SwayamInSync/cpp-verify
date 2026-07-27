// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify --check-ub %s 2>&1 | FileCheck %s --check-prefix=VERIFY

spec bool valid(int *p, int n) { return true; }

int shifted_marker(int *p, int n)
  pre(valid(p + 1, n))
  post(result == 0)
{
  return 0;
}

int disjunctive_marker(int *p, int n)
  pre(valid(p, n) || n == 0)
  post(result == 0)
{
  return 0;
}

int duplicate_marker(int *p, int n)
  pre(valid(p, n) && valid(p, n))
  post(result == 0)
{
  return 0;
}

// VERIFY-DAG: error: shifted_marker: valid marker requires a bare complete-object pointer and an integer element count
// VERIFY-DAG: error: disjunctive_marker: valid marker must be a positive top-level conjunction clause
// VERIFY-DAG: error: duplicate_marker: multiple valid markers for the same pointer are unsupported
