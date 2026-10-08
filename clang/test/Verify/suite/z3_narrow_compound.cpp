// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

signed char valid_i8_compound_add(signed char x)
  cppverify::pre(x == 100)
  cppverify::post(cppverify::result == -56)
{
  x += 100;
  return x;
}

unsigned char valid_u8_compound_multiply(unsigned char x)
  cppverify::pre(x == 200)
  cppverify::post(cppverify::result == 144)
{
  x *= 2;
  return x;
}

signed short valid_i16_compound_shift(signed short x)
  cppverify::pre(x == 1000)
  cppverify::post(cppverify::result == 8000)
{
  x <<= 3;
  return x;
}

signed char invalid_i8_compound_result(signed char x)
  cppverify::pre(x == 100)
  cppverify::post(cppverify::result == 44)
{
  x += 100;
  return x;
}

// VERIFY-DAG: Verified: valid_i8_compound_add
// VERIFY-DAG: Verified: valid_u8_compound_multiply
// VERIFY-DAG: Verified: valid_i16_compound_shift
// VERIFY-DAG: error: verification failed: invalid_i8_compound_result
