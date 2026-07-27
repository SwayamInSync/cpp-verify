// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

void set_value(int &value, int next)
  modifies(value)
  post(value == next)
{
  value = next;
}

void set_pair(int &left, int &right, int next)
  modifies(left, right)
  post(left == next && right == next)
{
  left = next;
  right = next;
}

void wrong_reference_post(int &value)
  modifies(value)
  post(value == 2)
{
  value = 1;
}

void missing_reference_modifies(int &value)
  post(value == 1)
{
  value = 1;
}

void wrong_reference_old(int &value)
  pre(value < 2147483647)
  modifies(value)
  post(value == old(value))
{
  ++value;
}

void wrong_reference_frame(int &allowed, int &forbidden)
  modifies(allowed)
{
  forbidden = 1;
}

void alias_without_permission(int *value)
  pre(value != nullptr)
  modifies(*value)
{
  set_pair(*value, *value, 4);
}

void nullable_reference_actual(int *value)
  modifies(*value)
{
  set_value(*value, 3);
}

void opaque_second(int &first, int &second)
  post(second == 1);

void implicit_effect_exceeds_frame(int *allowed, int *preserved)
  pre(allowed != nullptr && preserved != nullptr && *preserved == 0)
  modifies(allowed[0])
  post(*preserved == 0)
{
  opaque_second(*allowed, *preserved);
}

void nonterminating_reference_store(int &value)
  pre(value == 0)
  modifies(value)
  decreases(0)
{
  value = 1;
  if (value == 1) {
    value = 0;
    nonterminating_reference_store(value);
  }
}

void opaque_loop_effect(int &value)
  pre(value == value);

void implicit_effect_in_loop(int &value)
  pre(value == 0)
  post(value == 0)
{
  int iteration = 0;
  while (iteration < 1)
    invariant(iteration >= 0 && iteration <= 1)
    decreases(1 - iteration)
  {
    opaque_loop_effect(value);
    ++iteration;
  }
}

// VERIFY-DAG: Verified: set_value
// VERIFY-DAG: Verified: set_pair
// VERIFY-DAG: error: verification failed: wrong_reference_post
// VERIFY-DAG: error: verification failed: missing_reference_modifies
// VERIFY-DAG: error: verification failed: wrong_reference_old
// VERIFY-DAG: error: verification failed: wrong_reference_frame
// VERIFY-DAG: error: verification failed: alias_without_permission
// VERIFY-DAG: error: verification failed: nullable_reference_actual
// VERIFY-DAG: error: verification failed: implicit_effect_exceeds_frame
// VERIFY-DAG: error: decreases failed: nonterminating_reference_store
// VERIFY-DAG: error: verification failed: implicit_effect_in_loop
