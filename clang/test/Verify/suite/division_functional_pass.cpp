// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Division and modulo are modeled (signed bvsdiv / bvsrem, matching C++):
// a / b and a % b have their true values, and % follows the dividend's sign.
int divmod(int a, int b)
  pre(b > 0 && a >= 0 && a <= 1000)
  post(result == a / b && result >= 0 && a % b >= 0)
{
  return a / b;
}
// VERIFY: Verified: divmod
