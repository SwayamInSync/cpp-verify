// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --backend=bmc --unroll=3 %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int sum_first_n(int n)
  cppverify::pre(n >= 0 && n <= 3)
  cppverify::post(cppverify::result >= 0)
{
  int s = 0;
  int i = 0;
  while (i < n)
    cppverify::invariant(s >= 0)
    cppverify::invariant(i >= 0)
  {
    s = s + i;
    i = i + 1;
  }
  return s;
}

// VERIFY: Verified: sum_first_n