// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY
// Tier-1: lexicographic decreases tuple. (i, j) strictly decreases each
// iteration in lex order -- j falls while i is fixed, and when j resets i drops.
int countdown2(int a, int b)
  cppverify::pre(a >= 0 && b >= 0 && a <= 5 && b <= 5)
  cppverify::post(cppverify::result >= 0)
{
  int i = a;
  int j = b;
  while (i > 0 || j > 0)
    cppverify::invariant(i >= 0 && j >= 0)
    cppverify::decreases(i, j)
  {
    if (j > 0) {
      j = j - 1;
    } else {
      i = i - 1;
      j = b;
    }
  }
  return 0;
}
// VERIFY: Verified: countdown2
