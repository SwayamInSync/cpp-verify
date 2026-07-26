// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int external_increment(int value)
  pre(value < 2147483647)
  post(result == value + 1);

int valid_external_call(int value)
  pre(value < 2147483647)
  post(result == value + 1)
{
  return external_increment(value);
}

int invalid_external_call(int value)
  post(result == value + 1)
{
  return external_increment(value);
}

// VERIFY-DAG: warning: assuming external contract: external_increment
// VERIFY-DAG: Verified: valid_external_call
// VERIFY-DAG: error: verification failed: invalid_external_call
