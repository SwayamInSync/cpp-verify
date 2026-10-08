// RUN: %cpp-verify --backend=bmc --unroll=2 %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int nested_sum(int n)
  cppverify::pre(n >= 0 && n <= 1)
  cppverify::post(cppverify::result >= 0)
{
  int s = 0;
  int i = 0;
  while (i < n)
    cppverify::invariant(s >= 0)
  {
    int j = 0;
    while (j < 1)
      cppverify::invariant(j >= 0)
    {
      s = s + 1;
      j = j + 1;
    }
    i = i + 1;
  }
  return s;
}

// VERIFY: Verified: nested_sum