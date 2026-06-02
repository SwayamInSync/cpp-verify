// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int max2(int a, int b)
  pre(a >= -1000 && b >= -1000 && a <= 1000 && b <= 1000)
  post(result >= a && result >= b)
{
  return a >= b ? a : b;
}

int abs_safe(int x)
  pre(x >= -1000 && x <= 1000)
  post(result >= 0)
{
  return x < 0 ? -x : x;
}

int sum_to_n(int n)
  pre(n >= 0 && n <= 20)
  post(result >= 0)
{
  int s = 0;
  for (int i = 0; i < n; ++i)
    s = s + 1;
  return s;
}

int while_countdown(int n)
  pre(n >= 0 && n <= 10)
  post(result == 0)
{
  while (n > 0)
    n = n - 1;
  return n;
}

// VERIFY-DAG: verified: max2
// VERIFY-DAG: verified: abs_safe
// VERIFY-DAG: verified: sum_to_n
// VERIFY-DAG: verified: while_countdown