// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify --check-ub %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Layer-A UB inside a loop: the invariant does not bound s, so s + i can
// overflow on some iteration. The obligation is checked in the inductive step.
int sum(int n)
  cppverify::pre(n >= 0)
  cppverify::post(cppverify::result >= 0)
{
  int s = 0;
  int i = 0;
  while (i < n)
    cppverify::invariant(i >= 0 && s >= 0)
    cppverify::decreases(n - i)
  {
    s = s + i;
    i = i + 1;
  }
  return s;
}
// VERIFY: verification failed
