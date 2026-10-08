// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY

int increment(int value)
  cppverify::pre(value < 2147483647)
  cppverify::post(cppverify::result == value + 1);

void set_value(int *target, int value)
  cppverify::pre(target != nullptr)
  cppverify::modifies(*target)
  cppverify::post(*target == value);

int valid_forward_call(int value)
  cppverify::pre(value < 2147483647)
  cppverify::post(cppverify::result == value + 1)
{
  return increment(value);
}

void valid_forward_modifies(int *target)
  cppverify::pre(target != nullptr)
  cppverify::modifies(*target)
  cppverify::post(*target == 42)
{
  set_value(target, 42);
}

int invalid_forward_call(int value)
  cppverify::post(cppverify::result == value + 1)
{
  return increment(value);
}

int increment(int value) {
  return value + 1;
}

void set_value(int *target, int value) {
  *target = value;
}

// VERIFY-DAG: Verified: increment
// VERIFY-DAG: Verified: set_value
// VERIFY-DAG: Verified: valid_forward_call
// VERIFY-DAG: Verified: valid_forward_modifies
// VERIFY-DAG: error: verification failed: invalid_forward_call
