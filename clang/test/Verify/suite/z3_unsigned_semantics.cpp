// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int valid_unsigned_max(unsigned x)
  post(x <= 0xffffffffU)
{
  return 0;
}

int valid_unsigned_div_rem(unsigned x)
  pre(x == 0xffffffffU)
  post(x / 2U == 0x7fffffffU)
  post(x % 2U == 1U)
{
  return 0;
}

int valid_mixed_conversion(int x, unsigned y)
  pre(x == -1 && y == 1U)
  post(x > y)
{
  return 0;
}

int invalid_unsigned_upper_half(unsigned x)
  post(x <= 0x7fffffffU)
{
  return 0;
}

int invalid_mixed_conversion(int x, unsigned y)
  pre(x == -1 && y == 1U)
  post(x < y)
{
  return 0;
}

// VERIFY-DAG: Verified: valid_unsigned_max
// VERIFY-DAG: Verified: valid_unsigned_div_rem
// VERIFY-DAG: Verified: valid_mixed_conversion
// VERIFY-DAG: error: verification failed: invalid_unsigned_upper_half
// VERIFY-DAG: error: verification failed: invalid_mixed_conversion
