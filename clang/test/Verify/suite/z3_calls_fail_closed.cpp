// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int overloaded(int x)
  post(result == x)
{
  return x;
}

long overloaded(long x)
  post(result == x)
{
  return x;
}

void opaque_side_effect();
int global_state;

template <typename T>
int unsupported_template(T)
  post(result == 0)
{
  return 0;
}

int calls_uncontracted()
  post(result == 0)
{
  opaque_side_effect();
  return 0;
}

int reads_global_state()
  post(result == result)
{
  return global_state;
}

int *unsupported_pointer_compound(int *pointer)
  post(result == result)
{
  pointer += 1;
  return pointer;
}

long unsupported_pointer_difference(int *left, int *right)
  post(result == result)
{
  return left - right;
}

int *unsupported_forged_pointer()
  post(result == result)
{
  return (int *)1;
}

int unsupported_switch(int x)
  post(result >= 0)
{
  switch (x) {
  case 0:
    return 0;
  default:
    return 1;
  }
}

int unsupported_evaluated_expression(int x)
  pre(x == 2147483647)
  post(result == 0)
{
  x + 1;
  return 0;
}

int unsupported_conditionless_for()
  post(result == 0)
{
  for (;;) {
  }
}

void unsupported_cross_type_alias(int *value, unsigned char *byte)
  aliases(value, byte)
  modifies(*byte)
{
  *byte = 0;
}

int unsupported_recursive_exec(int n)
  post(result == 0)
{
  return unsupported_recursive_exec(n);
}

// VERIFY-DAG: error: calls_uncontracted: call to function without a verification contract: opaque_side_effect
// VERIFY-DAG: error: reads_global_state: global variable access is unsupported: global_state
// VERIFY-DAG: error: unsupported_pointer_compound: pointer compound assignment is unsupported
// VERIFY-DAG: error: unsupported_pointer_difference: pointer subtraction is unsupported without same-allocation provenance
// VERIFY-DAG: error: unsupported_forged_pointer: unsupported explicit pointer or aggregate cast
// VERIFY-DAG: error: unsupported_switch: unsupported statement: SwitchStmt
// VERIFY-DAG: error: unsupported_evaluated_expression: unsupported expression statement
// VERIFY-DAG: error: unsupported_conditionless_for: conditionless for loops are unsupported
// VERIFY-DAG: error: unsupported_cross_type_alias: aliases between different pointee types are unsupported
// VERIFY-DAG: error: unsupported_recursive_exec: recursive executable functions require decreases
// VERIFY-DAG: error: unsupported_template: function template verification is unsupported
