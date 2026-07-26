// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int assigned_before_read()
  post(result == 7)
{
  int value;
  value = 7;
  return value;
}

int initialized_on_both_branches(bool choose_first)
  post(result == 1 || result == 2)
{
  int value;
  if (choose_first)
    value = 1;
  else
    value = 2;
  return value;
}

int initialized_on_fallthrough_branch(bool return_early)
  post(result == 0 || result == 4)
{
  int value;
  if (return_early)
    return 0;
  else
    value = 4;
  return value;
}

int unreachable_uninitialized_read(bool choose_first)
  post(result == 1 || result == 2)
{
  int value;
  if (choose_first)
    return 1;
  else
    return 2;
  return value;
}

// VERIFY-DAG: Verified: assigned_before_read
// VERIFY-DAG: Verified: initialized_on_both_branches
// VERIFY-DAG: Verified: initialized_on_fallthrough_branch
// VERIFY-DAG: Verified: unreachable_uninitialized_read
