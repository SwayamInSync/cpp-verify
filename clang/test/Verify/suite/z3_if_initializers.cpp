// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int valid_if_initializer(int value)
  pre(value == 4)
  post(result == 5)
{
  if (int next = value + 1; next > 0)
    return next;
  return 0;
}

int valid_if_condition_declaration(int value)
  pre(value == 4)
  post(result == 4)
{
  if (int condition = value)
    return condition;
  return 0;
}

int invalid_if_initializer_claim(int value)
  pre(value == 4)
  post(result == 4)
{
  if (int next = value + 1; next > 0)
    return next;
  return 0;
}

// VERIFY-DAG: Verified: valid_if_initializer
// VERIFY-DAG: Verified: valid_if_condition_declaration
// VERIFY-DAG: error: verification failed: invalid_if_initializer_claim
