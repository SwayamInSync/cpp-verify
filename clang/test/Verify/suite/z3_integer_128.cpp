// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

using i128 = __int128;
using u128 = unsigned __int128;

i128 valid_i128_add(i128 x)
  pre(x == ((i128)1 << 100))
  post(result == (((i128)1 << 100) + 1))
{
  return x + 1;
}

i128 valid_i128_shift(i128 x)
  pre(x == 1)
  post(result == ((i128)1 << 100))
{
  return x << 100;
}

i128 valid_i128_sign_bit()
  post(result == (-((i128)1 << 126) - ((i128)1 << 126)))
{
  return (i128)1 << 127;
}

u128 valid_u128_wrap(u128 x)
  pre(x == ~(u128)0)
  post(result == 0)
{
  return x + 1;
}

i128 unsafe_i128_add(i128 x)
  pre(x == (((i128)1 << 126) + (((i128)1 << 126) - 1)))
  post(result == result)
{
  return x + 1;
}

i128 unsafe_i128_division(i128 x)
  pre(x == (-((i128)1 << 126) - ((i128)1 << 126)))
  post(result == result)
{
  return x / -1;
}

i128 unsafe_i128_negation(i128 x)
  pre(x == (-((i128)1 << 126) - ((i128)1 << 126)))
  post(result == result)
{
  return -x;
}

i128 unsafe_i128_left_shift(i128 x)
  pre(x == 2)
  post(result == result)
{
  return x << 127;
}

// VERIFY-DAG: Verified: valid_i128_add
// VERIFY-DAG: Verified: valid_i128_shift
// VERIFY-DAG: Verified: valid_i128_sign_bit
// VERIFY-DAG: Verified: valid_u128_wrap
// VERIFY-DAG: error: verification failed: unsafe_i128_add
// VERIFY-DAG: error: verification failed: unsafe_i128_division
// VERIFY-DAG: error: verification failed: unsafe_i128_negation
// VERIFY-DAG: error: verification failed: unsafe_i128_left_shift
