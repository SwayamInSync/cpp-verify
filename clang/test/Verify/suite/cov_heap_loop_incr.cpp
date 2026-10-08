// RUN: %cpp-verify %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY

int loop_incr(int n, int *p)
  cppverify::pre(n >= 0 && n <= 2 && p != 0)
  cppverify::pre(*p == 0)
  cppverify::modifies(*p)
  cppverify::post(cppverify::result >= 0)
{
  int i = 0;
  while (i < n)
    cppverify::invariant(i >= 0 && i <= n)
    cppverify::invariant(*p == i)
    cppverify::decreases(n - i)
  {
    *p = *p + 1;
    i = i + 1;
  }
  return i;
}

// VERIFY: Verified: loop_incr