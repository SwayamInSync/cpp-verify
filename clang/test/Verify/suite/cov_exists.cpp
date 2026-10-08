// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int bounded(int n)
  cppverify::pre(n > 0 && n <= 4)
  cppverify::pre(cppverify::exists(i, 0, n, i >= 0 && i < n))
  cppverify::post(cppverify::result >= 0)
{
  return n - 1;
}

// VERIFY: Verified: bounded