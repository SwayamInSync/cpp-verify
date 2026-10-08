// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY

int set_and_return(int *p, int value)
  cppverify::pre(p != nullptr)
  cppverify::modifies(*p)
  cppverify::post(*p == value && cppverify::result == value)
{
  *p = value;
  return value;
}

int add_values(int x, int y)
  cppverify::pre(x >= 0 && x <= 100 && y >= 0 && y <= 100)
  cppverify::post(cppverify::result == x + y)
{
  return x + y;
}

int valid_nested_call_with_independent_argument(int *p)
  cppverify::pre(p != nullptr)
  cppverify::modifies(*p)
  cppverify::post(cppverify::result == 8)
{
  return add_values(set_and_return(p, 7), 1);
}

// VERIFY-DAG: Verified: set_and_return
// VERIFY-DAG: Verified: add_values
// VERIFY-DAG: Verified: valid_nested_call_with_independent_argument
