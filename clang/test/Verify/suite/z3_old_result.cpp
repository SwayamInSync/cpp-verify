// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int inc(int x)
  pre(x >= 0 && x < 1000)
  post(result == old(x) + 1)
{
  return x + 1;
}

int id(int x)
  pre(true)
  post(result == old(x))
{
  return x;
}

// VERIFY-DAG: Verified: inc
// VERIFY-DAG: Verified: id