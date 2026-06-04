// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int sum_for(int n)
  pre(n >= 0 && n <= 3)
  post(result >= 0)
{
  int s = 0;
  int i = 0;
  for (; i < n;)
    // s == i (<= n <= 3) keeps s + 1 from overflowing — inductive invariant.
    invariant(s == i && i >= 0 && i <= n)
  {
    s = s + 1;
    i = i + 1;
  }
  return s;
}

// VERIFY: Verified: sum_for