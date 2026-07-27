// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

void set_value(int &value, int next)
  modifies(value)
  post(value == next)
{
  value = next;
}

int read_value(const int &value)
  post(result == value)
{
  return value;
}

struct Pair {
  int first;
  int second;
};

struct WithReference {
  int &value;
};

int local_actual()
  post(result == 2)
{
  int value = 1;
  set_value(value, 2);
  return value;
}

int temporary_actual()
  post(result == 1)
{
  return read_value(1);
}

int local_reference(int *value)
  pre(value != nullptr)
{
  int &alias = *value;
  return alias;
}

int &reference_return(int &value) pre(true) {
  return value;
}

int record_reference(Pair &value)
  post(result == value.first)
{
  return value.first;
}

int rvalue_reference(int &&value)
  post(result == value)
{
  return value;
}

int volatile_reference(volatile int &value)
  post(result == value)
{
  return value;
}

int pointer_reference(int *&value)
  post(result == 0)
{
  return value == nullptr ? 0 : 1;
}

int reference_member(WithReference value)
  post(result == value.value)
{
  return value.value;
}

spec int spec_reference(const int &value) {
  return value;
}

proof void proof_reference(const int &value)
  post(value == value)
{
}

int address_of_reference(int &value)
  post(result == value)
{
  int *pointer = &value;
  return *pointer;
}

int set_and_return(int &value)
  modifies(value)
  post(value == 1 && result == 1)
{
  value = 1;
  return 1;
}

int pick_second(int first, int second)
  post(result == second)
{
  return second;
}

int order_dependent_reference_read(int &value)
  pre(value == 0)
  modifies(value)
{
  return pick_second(set_and_return(value), value);
}

int order_dependent_subscript_read(int *value)
  pre(value != nullptr && value[0] == 0)
  modifies(*value)
{
  return pick_second(set_and_return(*value), value[0]);
}

int opaque_reference(int &value)
  post(value == 1 && result == 1);

int order_dependent_implicit_effect(int &value)
  pre(value == 0)
{
  return pick_second(opaque_reference(value), value);
}

void conditional_reference_actual(bool choose, int *value)
  pre(value != nullptr)
  modifies(*value)
{
  set_value(choose ? *value : *value, 2);
}

// VERIFY-DAG: error: local_actual: reference arguments require another reference parameter or a direct pointer dereference
// VERIFY-DAG: error: temporary_actual: reference arguments require another reference parameter or a direct pointer dereference
// VERIFY-DAG: error: local_reference: unsupported C++ type in verification: int &
// VERIFY-DAG: error: reference_return: unsupported C++ type in verification: int &
// VERIFY-DAG: error: record_reference: unsupported C++ type in verification: Pair &
// VERIFY-DAG: error: rvalue_reference: unsupported C++ type in verification: int &&
// VERIFY-DAG: error: volatile_reference: unsupported C++ type in verification: volatile int &
// VERIFY-DAG: error: pointer_reference: unsupported C++ type in verification: int *&
// VERIFY-DAG: error: reference_member: unsupported C++ type in verification: WithReference
// VERIFY-DAG: error: spec_reference: unsupported C++ type in verification: const int &
// VERIFY-DAG: error: proof_reference: unsupported C++ type in verification: const int &
// VERIFY-DAG: error: address_of_reference: unsupported unary operator
// VERIFY-DAG: error: order_dependent_reference_read: call arguments have order-dependent heap evaluations
// VERIFY-DAG: error: order_dependent_subscript_read: call arguments have order-dependent heap evaluations
// VERIFY-DAG: error: order_dependent_implicit_effect: call arguments have order-dependent heap evaluations
// VERIFY-DAG: error: conditional_reference_actual: reference arguments require another reference parameter or a direct pointer dereference
