// RUN: %cpp-verify %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY

bool all_small(int n)
  cppverify::pre(n >= 2 && n <= 4)
  cppverify::pre(cppverify::forall(i, 0, n, i >= 0 && i < n))
{
  return true;
}

// VERIFY: Verified: all_small