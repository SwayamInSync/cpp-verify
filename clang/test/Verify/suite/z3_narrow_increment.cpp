// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

signed char valid_i8_increment(signed char value)
  pre(value == 127)
  post(result == -128)
{
  ++value;
  return value;
}

signed char valid_i8_decrement(signed char value)
  pre(value == -128)
  post(result == 127)
{
  value--;
  return value;
}

void valid_i8_pointer_increment(signed char *value)
  pre(value != nullptr && *value == 127)
  modifies(*value)
  post(*value == -128)
{
  ++*value;
}

signed char invalid_i8_increment_claim(signed char value)
  pre(value == 127)
  post(result == 127)
{
  ++value;
  return value;
}

// VERIFY-DAG: Verified: valid_i8_increment
// VERIFY-DAG: Verified: valid_i8_decrement
// VERIFY-DAG: Verified: valid_i8_pointer_increment
// VERIFY-DAG: error: verification failed: invalid_i8_increment_claim
