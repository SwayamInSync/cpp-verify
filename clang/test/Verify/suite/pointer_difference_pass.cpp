// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

long abstract_unit_difference(int *pointer)
  pre(pointer != nullptr)
  post(result == 1)
{
  return (pointer + 1) - pointer;
}

long abstract_reverse_difference(int *pointer)
  pre(pointer != nullptr)
  post(result == -1)
{
  return pointer - (pointer + 1);
}

long abstract_zero_difference(int *pointer)
  pre(pointer != nullptr)
  post(result == 0)
{
  return (pointer + 0) - (pointer - 0);
}

long unit_pointer_difference(int *pointer)
  pre(pointer != nullptr)
  post(result == 1)
{
  return (pointer + 1) - pointer;
}

long dynamic_unit_difference(int value)
  post(result == 1)
{
  int *pointer = new int(value);
  long distance = (pointer + 1) - pointer;
  delete pointer;
  return distance;
}

long dynamic_reverse_difference(int value)
  post(result == -1)
{
  int *pointer = new int(value);
  long distance = pointer - (pointer + 1);
  delete pointer;
  return distance;
}

long dynamic_alias_difference(int value)
  post(result == 0)
{
  int *owner = new int(value);
  int *alias = owner;
  long distance = alias - owner;
  delete owner;
  return distance;
}

long modular_dynamic_difference(int value)
  post(result == 1)
{
  int *owner = new int(value);
  int *alias = owner;
  long distance = unit_pointer_difference(alias);
  delete owner;
  return distance;
}

// VERIFY-DAG: Verified: abstract_unit_difference
// VERIFY-DAG: Verified: abstract_reverse_difference
// VERIFY-DAG: Verified: abstract_zero_difference
// VERIFY-DAG: Verified: unit_pointer_difference
// VERIFY-DAG: Verified: dynamic_unit_difference
// VERIFY-DAG: Verified: dynamic_reverse_difference
// VERIFY-DAG: Verified: dynamic_alias_difference
// VERIFY-DAG: Verified: modular_dynamic_difference
