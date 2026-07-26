// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

double unsupported_float(double x)
  post(result == x)
{
  return x;
}

struct WithArray {
  int values[2];
};

int unsupported_aggregate(WithArray value)
  post(result == 0)
{
  return value.values[0];
}

int unsupported_reference(int &value)
  post(result == value)
{
  return value;
}

int unsupported_pointer_indirection(int **value)
  post(result == 0)
{
  return value == nullptr ? 0 : 1;
}

// VERIFY-DAG: error: unsupported_float: unsupported C++ type in verification: double
// VERIFY-DAG: error: unsupported_aggregate: unsupported C++ type in verification: WithArray
// VERIFY-DAG: error: unsupported_reference: unsupported C++ type in verification: int &
// VERIFY-DAG: error: unsupported_pointer_indirection: unsupported C++ type in verification: int **
