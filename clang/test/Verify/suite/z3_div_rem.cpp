// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int valid_division(int x)
  cppverify::pre(x == 10)
  cppverify::post(cppverify::result == 2)
{
  return x / 5;
}

int valid_negative_remainder(int x)
  cppverify::pre(x == -5)
  cppverify::post(cppverify::result == -1)
{
  return x % 2;
}

int invalid_division(int x)
  cppverify::pre(x == 10)
  cppverify::post(cppverify::result == 2)
{
  return x / 2;
}

int invalid_remainder(int x)
  cppverify::pre(x == 5)
  cppverify::post(cppverify::result == 0)
{
  return x % 2;
}

// VERIFY-DAG: Verified: valid_division
// VERIFY-DAG: Verified: valid_negative_remainder
// VERIFY-DAG: error: verification failed: invalid_division
// VERIFY-DAG: error: verification failed: invalid_remainder
