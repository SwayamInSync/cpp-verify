// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --check-ub %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// strlen: correct AND memory-safe in one proof (the scan stays in bounds).
cppverify::spec bool valid(int* p, int n) { return true; }
int slen(int* s, int n)
  cppverify::pre(valid(s, n) && n >= 1 && n <= 1000 && s[n - 1] == 0)
  cppverify::post(cppverify::result >= 0 && cppverify::result < n && s[cppverify::result] == 0)
{
  int i = 0;
  while (s[i] != 0) cppverify::invariant(0 <= i && i < n) cppverify::decreases(n - i) { i = i + 1; }
  return i;
}
// VERIFY: Verified: slen
