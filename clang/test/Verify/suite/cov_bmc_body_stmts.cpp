// RUN: %cpp-verify --backend=bmc --unroll=2 %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY

cppverify::spec int bump(int x) { return x + 1; }

int loop_mix(int n, int *p)
  cppverify::pre(n >= 0 && n <= 1 && p != 0)
  cppverify::modifies(*p)
  cppverify::post(cppverify::result >= 0)
{
  int i = 0;
  int s = 0;
  while (i < n)
    cppverify::invariant(s >= 0)
  {
    cppverify::ghost {
      cppverify::reveal(bump);
      cppverify::check(bump(s) == s + 1);
    }
    cppverify::check(i >= 0);
    if (i == 0)
      s = s + 1;
    else
      s = s + 0;
    *p = s;
    i = i + 1;
  }
  return s;
}

// VERIFY: Verified: loop_mix