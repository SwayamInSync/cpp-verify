// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int abs(int x)
  pre(x != (-2147483648))
  post(result >= 0)
{
  return x < 0 ? -x : x;
}

// VERIFY: Verified: abs