// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

struct Pair {
  int first;
  int second;
};

int uninitialized_scalar()
  post(result == result)
{
  int value;
  return value;
}

int uninitialized_field()
  post(result == result)
{
  Pair pair;
  pair.first = 1;
  return pair.second;
}

int initialized_on_one_branch(bool initialize)
  post(result == result)
{
  int value;
  if (initialize)
    value = 1;
  return value;
}

// VERIFY-DAG: error: uninitialized_scalar: read of uninitialized local value: value
// VERIFY-DAG: error: uninitialized_field: read of uninitialized local value: pair.second
// VERIFY-DAG: error: initialized_on_one_branch: read of uninitialized local value: value
