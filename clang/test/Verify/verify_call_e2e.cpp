// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int abs_val(int x)
  pre(x != (-2147483647 - 1))
  post(result >= 0)
{
  return x < 0 ? -x : x;
}

int use_abs(int x)
  pre(x != (-2147483647 - 1))
  post(result >= 0)
{
  int y = abs_val(x);
  return y;
}

// VERIFY: Verified: abs_val
// VERIFY: Verified: use_abs