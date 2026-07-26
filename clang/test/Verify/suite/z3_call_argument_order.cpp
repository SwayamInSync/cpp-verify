// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int set_and_return(int *p, int value)
  pre(p != nullptr)
  modifies(*p)
  post(*p == value && result == value)
{
  *p = value;
  return value;
}

int add_values(int x, int y)
  pre(x >= 0 && x <= 100 && y >= 0 && y <= 100)
  post(result == x + y)
{
  return x + y;
}

int unsupported_order_dependent_arguments(int *p)
  pre(p != nullptr)
  modifies(*p)
  post(result == result)
{
  return add_values(*p, set_and_return(p, 7));
}

// VERIFY-DAG: error: unsupported_order_dependent_arguments: call arguments have order-dependent heap evaluations
