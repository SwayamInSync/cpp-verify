// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

using i128 = __int128;
using u128 = unsigned __int128;

i128 valid_i128_add(i128 x)
  cppverify::pre(x == ((i128)1 << 100))
  cppverify::post(cppverify::result == (((i128)1 << 100) + 1))
{
  return x + 1;
}

i128 valid_i128_shift(i128 x)
  cppverify::pre(x == 1)
  cppverify::post(cppverify::result == ((i128)1 << 100))
{
  return x << 100;
}

i128 valid_i128_sign_bit()
  cppverify::post(cppverify::result == (-((i128)1 << 126) - ((i128)1 << 126)))
{
  return (i128)1 << 127;
}

u128 valid_u128_wrap(u128 x)
  cppverify::pre(x == ~(u128)0)
  cppverify::post(cppverify::result == 0)
{
  return x + 1;
}

i128 unsafe_i128_add(i128 x)
  cppverify::pre(x == (((i128)1 << 126) + (((i128)1 << 126) - 1)))
  cppverify::post(cppverify::result == cppverify::result)
{
  return x + 1;
}

i128 unsafe_i128_division(i128 x)
  cppverify::pre(x == (-((i128)1 << 126) - ((i128)1 << 126)))
  cppverify::post(cppverify::result == cppverify::result)
{
  return x / -1;
}

i128 unsafe_i128_negation(i128 x)
  cppverify::pre(x == (-((i128)1 << 126) - ((i128)1 << 126)))
  cppverify::post(cppverify::result == cppverify::result)
{
  return -x;
}

i128 unsafe_i128_left_shift(i128 x)
  cppverify::pre(x == 2)
  cppverify::post(cppverify::result == cppverify::result)
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
