// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// C++ % is the truncated remainder (sign of the dividend), so a negative
// dividend gives a non-positive remainder -- result >= 0 is false here.
int rem(int a, int b)
  pre(b > 0 && a >= -100 && a < 0)
  post(result >= 0)
{
  return a % b;
}
// VERIFY: verification failed
