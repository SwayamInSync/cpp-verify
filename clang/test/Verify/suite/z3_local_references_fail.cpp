// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

void set_value(int &target, int value)
  modifies(target)
  post(target == value)
{
  target = value;
}

void set_pair(int &left, int &right, int value)
  modifies(left, right)
  post(left == value && right == value)
{
  left = value;
  right = value;
}

void opaque_reference(int &value)
  post(value == 1);

int wrong_local_post()
  post(result == 0)
{
  int local = 0;
  set_value(local, 1);
  return local;
}

int same_local_without_aliases()
  post(result == 4)
{
  int local = 0;
  set_pair(local, local, 4);
  return local;
}

int nullable_local_reference(int *pointer)
  post(result == 0)
{
  int &alias = *pointer;
  return alias;
}

int external_local_reference()
  post(result == 1)
{
  int local = 0;
  opaque_reference(local);
  return local;
}

int recursive_local_reference(int value)
  pre(value >= 0)
  post(result == 0)
  decreases(value)
{
  int local = value;
  set_value(local, value);
  if (value == 0)
    return 0;
  return recursive_local_reference(value - 1);
}

// VERIFY-DAG: Verified: set_value
// VERIFY-DAG: Verified: set_pair
// VERIFY-DAG: error: verification failed: wrong_local_post
// VERIFY-DAG: error: verification failed: same_local_without_aliases
// VERIFY-DAG: error: verification failed: nullable_local_reference
// VERIFY-DAG: error: verification failed: external_local_reference
// VERIFY-DAG: error: decreases failed: recursive_local_reference
