// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int inc(int x)
  cppverify::pre(x >= 0 && x < 100)
  cppverify::post(cppverify::result == x + 1)
{
  return x + 1;
}

int bump(int x)
  cppverify::pre(x >= 0 && x < 99)
  cppverify::post(cppverify::result >= x)
{
  if (x < 50)
    return inc(x);
  return inc(inc(x));
}

// VERIFY-DAG: Verified: inc
// VERIFY-DAG: Verified: bump