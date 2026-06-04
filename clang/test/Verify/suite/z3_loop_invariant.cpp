// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int sum_loop(int n)
  pre(n >= 0 && n <= 15)
  post(result >= 0)
{
  int s = 0;
  int i = 0;
  while (i < n)
    // s == i bounds s by n (<= 15), so s + 1 cannot overflow: the invariant is
    // inductive under honest machine integers. (s >= 0 alone is NOT inductive —
    // from an arbitrary s = INT_MAX it fails to be preserved.)
    invariant(i >= 0 && i <= n && s == i)
    decreases(n - i)
  {
    s = s + 1;
    i = i + 1;
  }
  return s;
}

// VERIFY: Verified: sum_loop