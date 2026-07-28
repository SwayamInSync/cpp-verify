// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

void set_value(int &target, int value)
  modifies(target)
  post(target == value)
{
  target = value;
}

int set_and_return(int &target, int value)
  modifies(target)
  post(target == value && result == value)
{
  target = value;
  return value;
}

int pick_second(int first, int second)
  post(result == second)
{
  return second;
}

int uninitialized_local_actual()
  post(result == 1)
{
  int local;
  set_value(local, 1);
  return local;
}

int order_dependent_local()
  post(result == 0 || result == 1)
{
  int local = 0;
  return pick_second(set_and_return(local, 1), local);
}

int temporary_binding()
  post(result == 1)
{
  const int &alias = 1;
  return alias;
}

int conditional_binding(bool choose)
  post(result == 1 || result == 2)
{
  int first = 1;
  int second = 2;
  const int &alias = choose ? first : second;
  return alias;
}

struct Pair {
  int first;
  int second;
};

int conditional_field_binding(bool choose)
  post(result == 1)
{
  Pair value{1, 2};
  const int &alias = choose ? value.first : value.second;
  return alias;
}

int loop_local_declaration()
  post(result == 1)
{
  int iteration = 0;
  while (iteration < 1)
    invariant(iteration >= 0 && iteration <= 1)
    decreases(1 - iteration)
  {
    int local = 0;
    set_value(local, 1);
    ++iteration;
  }
  return iteration;
}

// VERIFY-DAG: error: uninitialized_local_actual: read of uninitialized local value: local
// VERIFY-DAG: error: order_dependent_local: call arguments have order-dependent heap evaluations
// VERIFY-DAG: error: temporary_binding: local references require a supported direct lvalue
// VERIFY-DAG: error: conditional_binding: local references require a supported direct lvalue
// Binding a reference directly to a field of a local record is now supported
// (see reference_local_object_lowering.cpp); only the temporary and
// conditional forms remain unsupported.
// VERIFY-DAG: error: conditional_field_binding: local references require a supported direct lvalue
// VERIFY-DAG: error: loop_local_declaration: addressable local declarations inside loops are unsupported
