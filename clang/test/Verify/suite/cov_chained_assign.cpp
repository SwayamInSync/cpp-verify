// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int step(int x)
  pre(x >= 0 && x < 100)
  post(result == x + 1)
{
  return x + 1;
}

int two_steps(int x)
  pre(x >= 0 && x < 98)
  post(result == x + 2)
{
  int t = step(step(x));
  return t;
}

// VERIFY-DAG: verified: step
// VERIFY-DAG: verified: two_steps