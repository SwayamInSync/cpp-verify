// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

unsigned char byte_value()
  cppverify::post(cppverify::result == 255)
{
  return 255;
}

int int_value()
  cppverify::post(cppverify::result == 300)
{
  return 300;
}

int minus_one()
  cppverify::post(cppverify::result == -1)
{
  return -1;
}

bool greater_than_one(unsigned value)
  cppverify::post(cppverify::result == (value > 1U))
{
  return value > 1U;
}

bool true_value()
  cppverify::post(cppverify::result)
{
  return true;
}

int valid_direct_result_widening()
  cppverify::post(cppverify::result == 255)
{
  return byte_value();
}

int valid_local_result_widening()
  cppverify::post(cppverify::result == 255)
{
  int value = byte_value();
  return value;
}

int valid_assignment_result_widening()
  cppverify::post(cppverify::result == 255)
{
  int value;
  value = byte_value();
  return value;
}

unsigned char valid_direct_result_narrowing()
  cppverify::post(cppverify::result == 44)
{
  return int_value();
}

int valid_bool_to_integer_result()
  cppverify::post(cppverify::result == 1)
{
  return true_value();
}

bool valid_integer_to_bool_result()
  cppverify::post(cppverify::result)
{
  return int_value();
}

bool valid_signed_to_unsigned_argument()
  cppverify::post(cppverify::result)
{
  return greater_than_one(-1);
}

bool valid_nested_result_argument_conversion()
  cppverify::post(cppverify::result)
{
  return greater_than_one(minus_one());
}

bool invalid_signed_to_unsigned_argument_claim()
  cppverify::post(!cppverify::result)
{
  return greater_than_one(-1);
}

// VERIFY-DAG: Verified: valid_direct_result_widening
// VERIFY-DAG: Verified: valid_local_result_widening
// VERIFY-DAG: Verified: valid_assignment_result_widening
// VERIFY-DAG: Verified: valid_direct_result_narrowing
// VERIFY-DAG: Verified: valid_bool_to_integer_result
// VERIFY-DAG: Verified: valid_integer_to_bool_result
// VERIFY-DAG: Verified: valid_signed_to_unsigned_argument
// VERIFY-DAG: Verified: valid_nested_result_argument_conversion
// VERIFY-DAG: error: verification failed: invalid_signed_to_unsigned_argument_claim
