// RUN: %clang_cc1 -std=c++17 -fverify-contracts -emit-obj -o %t.o %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

enum class State : unsigned { Idle, Ready };

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

void increment_value(int &value)
  pre(value < 2147483647)
  modifies(value)
  post(value == old(value) + 1)
{
  ++value;
}

void swap_values(int &left, int &right)
  modifies(left, right)
  post(left == old(right) && right == old(left))
{
  int temporary = left;
  left = right;
  right = temporary;
}

bool negate_value(bool &value)
  modifies(value)
  post(value == !old(value) && result == value)
{
  value = !value;
  return value;
}

void increment_unsigned(unsigned &value)
  pre(value < 4294967295U)
  modifies(value)
  post(value == old(value) + 1U)
{
  ++value;
}

void increment_short(short &value)
  pre(value >= 0 && value < 100)
  modifies(value)
  post(value == old(value) + 1)
{
  ++value;
}

void mark_ready(State &state)
  modifies(state)
  post(state == State::Ready)
{
  state = State::Ready;
}

void copy_value(int &target, const int &source)
  aliases(target, source)
  modifies(target)
  post(target == old(source))
{
  target = source;
}

void forward_set(int &value, int next)
  modifies(value)
  post(value == next)
{
  set_value(value, next);
}

void set_through_pointer(int *value, int next)
  pre(value != nullptr)
  modifies(*value)
  post(*value == next)
{
  set_value(*value, next);
}

int read_through_pointer(const int *value)
  pre(value != nullptr)
  post(result == *value)
{
  return read_value(*value);
}

void preserve_through_alias(int *value)
  pre(value != nullptr)
  modifies(*value)
  post(*value == old(*value))
{
  copy_value(*value, *value);
}

void declared_set(int &value, int next)
  modifies(value)
  post(value == next);

void declared_set(int &renamed, int replacement) {
  renamed = replacement;
}

int set_dynamic_reference()
  post(result == 7)
{
  int *value = new int(2);
  set_value(*value, 7);
  int observed = *value;
  delete value;
  return observed;
}

// VERIFY-DAG: Verified: set_value
// VERIFY-DAG: Verified: read_value
// VERIFY-DAG: Verified: increment_value
// VERIFY-DAG: Verified: swap_values
// VERIFY-DAG: Verified: negate_value
// VERIFY-DAG: Verified: increment_unsigned
// VERIFY-DAG: Verified: increment_short
// VERIFY-DAG: Verified: mark_ready
// VERIFY-DAG: Verified: copy_value
// VERIFY-DAG: Verified: forward_set
// VERIFY-DAG: Verified: set_through_pointer
// VERIFY-DAG: Verified: read_through_pointer
// VERIFY-DAG: Verified: preserve_through_alias
// VERIFY-DAG: Verified: declared_set
// VERIFY-DAG: Verified: set_dynamic_reference
