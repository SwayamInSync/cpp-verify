// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

unsigned valid_explicit_narrowing()
  cppverify::post(cppverify::result == 44U)
{
  unsigned value{300U};
  unsigned char narrowed = static_cast<unsigned char>(value);
  return static_cast<unsigned>(narrowed);
}

int valid_scalar_value_initialization()
  cppverify::post(cppverify::result == 0)
{
  int zero = int();
  bool false_value{};
  return false_value ? 1 : zero;
}

int valid_scalar_brace_assignment()
  cppverify::post(cppverify::result == 3)
{
  int value;
  value = {3};
  return value;
}

int valid_empty_brace_return()
  cppverify::post(cppverify::result == 0)
{
  return {};
}

bool valid_pointer_to_bool(int *pointer)
  cppverify::post(cppverify::result == (pointer != nullptr))
{
  return static_cast<bool>(pointer);
}

bool valid_implicit_pointer_to_bool(int *pointer)
  cppverify::post(cppverify::result == (pointer != nullptr))
{
  return pointer;
}

bool valid_integer_to_bool()
  cppverify::post(cppverify::result)
{
  return static_cast<bool>(2);
}

unsigned invalid_explicit_narrowing_claim()
  cppverify::post(cppverify::result == 300U)
{
  unsigned value{300U};
  unsigned char narrowed = static_cast<unsigned char>(value);
  return static_cast<unsigned>(narrowed);
}

bool invalid_integer_to_bool_claim()
  cppverify::post(!cppverify::result)
{
  return static_cast<bool>(2);
}

// VERIFY-DAG: Verified: valid_explicit_narrowing
// VERIFY-DAG: Verified: valid_scalar_value_initialization
// VERIFY-DAG: Verified: valid_scalar_brace_assignment
// VERIFY-DAG: Verified: valid_empty_brace_return
// VERIFY-DAG: Verified: valid_pointer_to_bool
// VERIFY-DAG: Verified: valid_implicit_pointer_to_bool
// VERIFY-DAG: Verified: valid_integer_to_bool
// VERIFY-DAG: error: verification failed: invalid_explicit_narrowing_claim
// VERIFY-DAG: error: verification failed: invalid_integer_to_bool_claim
