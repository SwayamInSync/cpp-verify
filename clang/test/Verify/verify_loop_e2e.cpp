// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int sum_first_n(int n)
  pre(n >= 0 && n <= 3)
  post(result >= 0)
{
  int s = 0;
  int i = 0;
  while (i < n)
    // s accumulates i each step; s <= i * n bounds it (i, n <= 3 so s <= 9),
    // making s + i overflow-free and the invariant inductive. s >= 0 alone is
    // not preserved from an arbitrary large s.
    invariant(s >= 0 && i >= 0 && i <= n && s <= i * n)
    decreases(n - i)
  {
    s = s + i;
    i = i + 1;
  }
  return s;
}

// VERIFY: Verified: sum_first_n