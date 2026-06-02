// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int add(int a, int b)
  pre(a >= 0 && b >= 0 && a <= 1000 && b <= 1000)
  post(result == a + b)
{
  return a + b;
}

int sub_nonneg(int a, int b)
  pre(a >= b && b >= 0)
  post(result == a - b)
{
  return a - b;
}

int mul_small(int a, int b)
  pre(a >= 0 && b >= 0 && a <= 10 && b <= 10)
  post(result == a * b)
{
  return a * b;
}

int cmp_chain(int x)
  pre(x >= 0 && x <= 5)
  post(result >= 0 && result <= 2)
{
  if (x < 2) return 0;
  if (x < 4) return 1;
  return 2;
}

// VERIFY-DAG: Verified: add
// VERIFY-DAG: Verified: sub_nonneg
// VERIFY-DAG: Verified: mul_small
// VERIFY-DAG: Verified: cmp_chain