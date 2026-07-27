// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

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

void set_aliases(int &left, int &right, int value)
  aliases(left, right)
  modifies(left, right)
  post(left == value && right == value)
{
  left = value;
  right = value;
}

void swap_values(int &left, int &right)
  modifies(left, right)
  post(left == old(right) && right == old(left))
{
  int temporary = left;
  left = right;
  right = temporary;
}

int identity(int value)
  post(result == value)
{
  return value;
}

void set_through_alias(int &target, int value)
  modifies(target)
  post(target == value)
{
  int &alias = target;
  alias = value;
}

void forward_reference_alias(int &target, int value)
  modifies(target)
  post(target == value)
{
  int &alias = target;
  set_value(alias, value);
}

void set_through_pointer_alias(int *target, int value)
  pre(target != nullptr)
  modifies(*target)
  post(*target == value)
{
  int &alias = *target;
  alias = value;
}

int local_actual(int value)
  pre(value < 2147483647)
  post(result == value + 1)
{
  int local = value;
  set_value(local, value + 1);
  return local;
}

int call_initialized_local(int value)
  post(result == value)
{
  int local = identity(value);
  set_value(local, value);
  return local;
}

int modular_local_alias(int value)
  post(result == value)
{
  int local = 0;
  set_through_alias(local, value);
  return local;
}

int forwarded_local_alias(int value)
  post(result == value)
{
  int local = 0;
  forward_reference_alias(local, value);
  return local;
}

int dynamic_pointer_alias()
  post(result == 5)
{
  int *pointer = new int(0);
  set_through_pointer_alias(pointer, 5);
  int observed = *pointer;
  delete pointer;
  return observed;
}

int pointer_binding_snapshot(int *first, int *second)
  pre(first != nullptr && second != nullptr && *first == 1 && *second == 2)
  modifies(*first)
  post(result == 4 && *second == 2)
{
  int &alias = *first;
  first = second;
  alias = 4;
  return alias;
}

void set_flag(bool &target)
  modifies(target)
  post(target)
{
  target = true;
}

bool bool_local()
  post(result)
{
  bool local = false;
  set_flag(local);
  return local;
}

int branch_local(bool choose)
  post(result == (choose ? 3 : 4))
{
  if (choose) {
    int chosen = 0;
    set_value(chosen, 3);
    return chosen;
  }
  int fallback = 0;
  set_value(fallback, 4);
  return fallback;
}

int local_alias(int value)
  pre(value < 2147483647)
  post(result == value + 1)
{
  int local = value;
  int &alias = local;
  ++alias;
  return local;
}

int chained_const_alias(int value)
  post(result == value)
{
  int local = value;
  int &first = local;
  const int &second = first;
  return second;
}

int distinct_locals()
  post(result == 6)
{
  int first = 0;
  int second = 0;
  set_pair(first, second, 3);
  return first + second;
}

int permitted_local_alias()
  post(result == 4)
{
  int local = 0;
  set_aliases(local, local, 4);
  return local;
}

bool local_swap()
  post(result)
{
  int left = 1;
  int right = 2;
  swap_values(left, right);
  return left == 2 && right == 1;
}

void preserve_parameter(int &parameter)
  pre(parameter == 7)
  post(parameter == 7)
{
  int local = 1;
  set_value(local, 2);
}

int branch_alias(bool choose)
  post(result == (choose ? 2 : 3))
{
  int local = 1;
  int &alias = local;
  if (choose)
    ++alias;
  else
    alias += 2;
  return local;
}

int loop_local(int count)
  pre(count >= 0 && count <= 100)
  post(result == count)
{
  int local = 0;
  set_value(local, 0);
  int iteration = 0;
  while (iteration < count)
    invariant(iteration >= 0 && iteration <= count)
    invariant(local == iteration)
    decreases(count - iteration)
  {
    ++local;
    ++iteration;
  }
  return local;
}

int loop_reference(int count)
  pre(count >= 0 && count <= 100)
  post(result == count)
{
  int local = 0;
  int iteration = 0;
  while (iteration < count)
    invariant(iteration >= 0 && iteration <= count)
    invariant(local == iteration)
    decreases(count - iteration)
  {
    int &alias = local;
    ++alias;
    ++iteration;
  }
  return local;
}

int pointer_alias(int *pointer)
  pre(pointer != nullptr && *pointer == 3)
  modifies(*pointer)
  post(*pointer == 4 && result == 4)
{
  int &alias = *pointer;
  ++alias;
  return alias;
}

enum class State : unsigned char {
  Off,
  On,
};

void set_state(State &target, State value)
  modifies(target)
  post(target == value)
{
  target = value;
}

bool enum_local()
  post(result)
{
  State state = State::Off;
  set_state(state, State::On);
  const State &alias = state;
  return alias == State::On;
}

// VERIFY-DAG: Verified: set_value
// VERIFY-DAG: Verified: set_pair
// VERIFY-DAG: Verified: set_aliases
// VERIFY-DAG: Verified: swap_values
// VERIFY-DAG: Verified: identity
// VERIFY-DAG: Verified: set_through_alias
// VERIFY-DAG: Verified: forward_reference_alias
// VERIFY-DAG: Verified: set_through_pointer_alias
// VERIFY-DAG: Verified: local_actual
// VERIFY-DAG: Verified: call_initialized_local
// VERIFY-DAG: Verified: modular_local_alias
// VERIFY-DAG: Verified: forwarded_local_alias
// VERIFY-DAG: Verified: dynamic_pointer_alias
// VERIFY-DAG: Verified: pointer_binding_snapshot
// VERIFY-DAG: Verified: set_flag
// VERIFY-DAG: Verified: bool_local
// VERIFY-DAG: Verified: branch_local
// VERIFY-DAG: Verified: local_alias
// VERIFY-DAG: Verified: chained_const_alias
// VERIFY-DAG: Verified: distinct_locals
// VERIFY-DAG: Verified: permitted_local_alias
// VERIFY-DAG: Verified: local_swap
// VERIFY-DAG: Verified: preserve_parameter
// VERIFY-DAG: Verified: branch_alias
// VERIFY-DAG: Verified: loop_local
// VERIFY-DAG: Verified: loop_reference
// VERIFY-DAG: Verified: pointer_alias
// VERIFY-DAG: Verified: set_state
// VERIFY-DAG: Verified: enum_local
