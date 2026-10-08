// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Heap soundness: returning i + 1 overshoots the terminator -> post fails.
int slen_bad(int* s, int n)
  cppverify::pre(s != nullptr && n >= 1 && n <= 1000 && s[n - 1] == 0)
  cppverify::post(cppverify::result >= 0 && cppverify::result < n && s[cppverify::result] == 0)
{
  int i = 0;
  while (s[i] != 0) cppverify::invariant(0 <= i && i < n) cppverify::decreases(n - i) { i = i + 1; }
  return i + 1;
}
// VERIFY: verification failed
