// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

struct Mixed {
  bool flag;
  unsigned value;
  unsigned long long wide;
};

Mixed valid_mixed_copy(Mixed input)
  post(result.flag == input.flag)
  post(result.value == input.value)
  post(result.wide == input.wide)
{
  return input;
}

bool valid_mixed_copy_call(Mixed input)
  post(result == input.flag)
{
  Mixed output = valid_mixed_copy(input);
  return output.flag;
}

unsigned long long valid_old_wide_field(Mixed input)
  post(result == old(input.wide))
{
  unsigned long long saved = input.wide;
  input.wide = 0;
  return saved;
}

Mixed invalid_bool_field_copy(Mixed input)
  post(result.flag != input.flag)
{
  return input;
}

// VERIFY-DAG: Verified: valid_mixed_copy
// VERIFY-DAG: Verified: valid_mixed_copy_call
// VERIFY-DAG: Verified: valid_old_wide_field
// VERIFY-DAG: error: verification failed: invalid_bool_field_copy
