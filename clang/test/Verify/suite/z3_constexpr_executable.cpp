// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

constexpr int increment(int value)
  pre(value < 2147483647)
  post(result == value + 1)
{
  return value + 1;
}

int valid_constexpr_executable_call(int value)
  pre(value < 2147483647)
  post(result == value + 1)
{
  return increment(value);
}

int invalid_constexpr_executable_precondition()
  post(result == -2147483648)
{
  return increment(2147483647);
}

// VERIFY-DAG: Verified: increment
// VERIFY-DAG: Verified: valid_constexpr_executable_call
// VERIFY-DAG: error: verification failed: invalid_constexpr_executable_precondition
