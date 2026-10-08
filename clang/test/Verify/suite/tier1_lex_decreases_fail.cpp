// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Tier-1: the body resets i = a after decrementing, so the tuple (i, j) does
// not decrease lexicographically -- termination fails.
int bad_lex(int a, int b)
  cppverify::pre(a >= 0 && b >= 0 && a <= 5 && b <= 5)
  cppverify::post(cppverify::result >= 0)
{
  int i = a;
  int j = b;
  while (i > 0 || j > 0)
    cppverify::invariant(i >= 0 && j >= 0)
    cppverify::decreases(i, j)
  {
    if (i > 0) { i = i - 1; } else { j = j - 1; }
    i = a;
  }
  return 0;
}
// VERIFY: verification failed
