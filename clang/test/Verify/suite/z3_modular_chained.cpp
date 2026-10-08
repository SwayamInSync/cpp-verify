// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY

int inc(int x)
  cppverify::pre(x >= 0 && x < 100)
  cppverify::post(cppverify::result == x + 1)
{
  return x + 1;
}

int inc_twice(int x)
  cppverify::pre(x >= 0 && x < 98)
  cppverify::post(cppverify::result == x + 2)
{
  return inc(inc(x));
}

// VERIFY-DAG: Verified: inc
// VERIFY-DAG: Verified: inc_twice