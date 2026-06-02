// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int sum_loop(int n)
  pre(n >= 0 && n <= 15)
  post(result >= 0)
{
  int s = 0;
  int i = 0;
  while (i < n)
    invariant(i >= 0 && i <= n && s >= 0)
    decreases(n - i)
  {
    s = s + 1;
    i = i + 1;
  }
  return s;
}

// VERIFY: verified: sum_loop