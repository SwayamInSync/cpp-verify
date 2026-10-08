// RUN: %cpp-verify %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY

int inc(int x)
  cppverify::pre(x >= 0 && x < 1000)
  cppverify::post(cppverify::result == x + 1)
{
  return x + 1;
}

int use_inc(int x)
  cppverify::pre(x >= 0 && x < 999)
  cppverify::post(cppverify::result == x + 1)
{
  return inc(x);
}

// VERIFY-DAG: Verified: inc
// VERIFY-DAG: Verified: use_inc