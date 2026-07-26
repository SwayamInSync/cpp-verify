// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

unsigned low_bit(unsigned x)
  post(result <= 1U)
{
  return x & 1U;
}

unsigned complement(unsigned x)
  post(result == 0xffffffffU - x)
{
  return ~x;
}

unsigned xor_self(unsigned x)
  post(result == 0U)
{
  return x ^ x;
}

unsigned safe_left_shift(unsigned x, unsigned amount)
  pre(x <= 65535U && amount < 16U)
  post((result >> amount) == x)
{
  return x << amount;
}

int safe_signed_left_shift(int x)
  pre(x >= 0 && x <= 1073741823)
  post(result == x * 2)
{
  return x << 1;
}

int safe_signed_left_sign_bit()
  post(result == (-2147483647 - 1))
{
  return 1 << 31;
}

int target_signed_right_shift()
  post(result == -1)
{
  return -1 >> 1;
}

unsigned bitwise_compound_assign(unsigned x)
  post(result <= 3U)
{
  x &= 7U;
  x ^= 4U;
  x |= 1U;
  return x & 3U;
}

int unsafe_shift_count(int x)
  pre(x == 1)
  post(result == result)
{
  return x << 32;
}

int unsafe_negative_shift_count(int x)
  pre(x == 1)
  post(result == result)
{
  return x << -1;
}

int unsafe_signed_left_overflow(int x)
  pre(x == 1073741824)
  post(result == result)
{
  return x << 2;
}

int unsafe_signed_left_negative(int x)
  pre(x == -1)
  post(result == result)
{
  return x << 1;
}

// VERIFY-DAG: Verified: low_bit
// VERIFY-DAG: Verified: complement
// VERIFY-DAG: Verified: xor_self
// VERIFY-DAG: Verified: safe_left_shift
// VERIFY-DAG: Verified: safe_signed_left_shift
// VERIFY-DAG: Verified: safe_signed_left_sign_bit
// VERIFY-DAG: Verified: target_signed_right_shift
// VERIFY-DAG: Verified: bitwise_compound_assign
// VERIFY-DAG: error: verification failed: unsafe_shift_count
// VERIFY-DAG: error: verification failed: unsafe_negative_shift_count
// VERIFY-DAG: error: verification failed: unsafe_signed_left_overflow
// VERIFY-DAG: error: verification failed: unsafe_signed_left_negative
