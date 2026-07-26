// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int valid_count(int n)
  pre(n >= 0 && n <= 20)
  post(result == n)
{
  int i = 0;
  while (i < n)
    invariant(i >= 0 && i <= n)
    decreases(n - i)
  {
    ++i;
  }
  return i;
}

int invalid_invariant_entry(int n)
  pre(n == 0)
  post(result == 0)
{
  int i = 0;
  while (i < n)
    invariant(i > 0)
  {
    ++i;
  }
  return i;
}

int invalid_invariant_preservation(int n)
  pre(n == 1)
  post(result >= 0)
{
  int i = 0;
  while (i < n)
    invariant(i == 0)
  {
    ++i;
  }
  return i;
}

int invalid_decreases(int n)
  pre(n > 0 && n <= 20)
  post(result == n)
{
  int i = 0;
  while (i < n)
    invariant(i >= 0 && i <= n)
    decreases(i)
  {
    ++i;
  }
  return i;
}

// VERIFY-DAG: Verified: valid_count
// VERIFY-DAG: error: verification failed: invalid_invariant_entry
// VERIFY-DAG: error: verification failed: invalid_invariant_preservation
// VERIFY-DAG: error: verification failed: invalid_decreases
