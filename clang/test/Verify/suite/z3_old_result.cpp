// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY

int inc(int x)
  cppverify::pre(x >= 0 && x < 1000)
  cppverify::post(cppverify::result == cppverify::old(x) + 1)
{
  return x + 1;
}

int id(int x)
  cppverify::pre(true)
  cppverify::post(cppverify::result == cppverify::old(x))
{
  return x;
}

// VERIFY-DAG: Verified: inc
// VERIFY-DAG: Verified: id