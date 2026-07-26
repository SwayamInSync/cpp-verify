// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

constexpr int assigned_absolute_value(int value) {
  int output;
  if (value < 0)
    output = -value;
  else
    output = value;
  return output;
}

constexpr int positive_or_zero(int value) {
  int output = 0;
  if (value > 0)
    output = value;
  return output;
}

constexpr int return_or_assign(int value) {
  int output;
  if (value < 0)
    return 0;
  else
    output = value;
  return output;
}

constexpr int guarded_division_assignment(int value) {
  int output = 0;
  if (value != 0)
    output = 10 / value;
  return output;
}

constexpr int unsafe_division_assignment(int value) {
  int output = 0;
  if (value == 0)
    output = 10 / value;
  return output;
}

spec int selected_value(bool choose_first, int first, int second) {
  int output;
  if (choose_first)
    output = first;
  else
    output = second;
  return output;
}

int valid_assigned_absolute_value(int value)
  pre(value != -2147483648)
  post(assigned_absolute_value(value) >= 0)
{
  return 0;
}

int valid_positive_or_zero(int value)
  post(positive_or_zero(value) >= 0)
{
  return 0;
}

int valid_return_or_assign(int value)
  post(return_or_assign(value) >= 0)
{
  return 0;
}

int valid_spec_branch_assignment(bool choose_first, int first, int second)
  post(selected_value(choose_first, first, second) ==
       (choose_first ? first : second))
{
  return 0;
}

int valid_guarded_division_assignment(int value)
  post(guarded_division_assignment(value) ==
       (value != 0 ? 10 / value : 0))
{
  return 0;
}

int invalid_assigned_absolute_min()
  post(assigned_absolute_value(-2147483648) == -2147483648)
{
  return 0;
}

int invalid_spec_branch_assignment()
  post(selected_value(true, 1, 2) == 2)
{
  return 0;
}

int invalid_unsafe_division_assignment()
  post(unsafe_division_assignment(0) == unsafe_division_assignment(0))
{
  return 0;
}

// VERIFY-DAG: Verified: valid_assigned_absolute_value
// VERIFY-DAG: Verified: valid_positive_or_zero
// VERIFY-DAG: Verified: valid_return_or_assign
// VERIFY-DAG: Verified: valid_spec_branch_assignment
// VERIFY-DAG: Verified: valid_guarded_division_assignment
// VERIFY-DAG: error: verification failed: invalid_assigned_absolute_min
// VERIFY-DAG: error: verification failed: invalid_spec_branch_assignment
// VERIFY-DAG: error: verification failed: invalid_unsafe_division_assignment
