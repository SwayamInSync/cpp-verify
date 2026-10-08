// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

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

int unsupported_order_dependent_arguments(int *p)
  cppverify::pre(p != nullptr)
  cppverify::modifies(*p)
  cppverify::post(cppverify::result == cppverify::result)
{
  return add_values(*p, set_and_return(p, 7));
}

// VERIFY-DAG: error: unsupported_order_dependent_arguments: call arguments have order-dependent heap evaluations
