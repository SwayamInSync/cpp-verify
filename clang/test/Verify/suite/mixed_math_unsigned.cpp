// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --check-ub --timeout=10000 %s 2>&1 | FileCheck %s

typedef __UINT64_TYPE__ uint64_t;
typedef __UINT8_TYPE__ uint8_t;

spec uint64_t math_quotient_128(uint64_t value) {
  return value / 128;
}

spec uint8_t math_remainder_128(uint64_t value) {
  return value % 128;
}

spec unsigned math_uleb_first_byte(uint64_t value) {
  return (value % 128) + (value >= 128 ? 128 : 0);
}

spec unsigned math_uleb_second_digit(uint64_t value) {
  return (value / 128) % 128;
}

uint64_t shift_matches_math_division(uint64_t value)
  post(result == math_quotient_128(value))
{
  return value >> 7;
}

uint8_t mask_matches_math_remainder(uint64_t value)
  post(result == math_remainder_128(value))
{
  return value & 0x7f;
}

uint64_t machine_division_matches_math(uint64_t value)
  post(result == math_quotient_128(value))
{
  return value / 128ULL;
}

uint8_t machine_remainder_matches_math(uint64_t value)
  post(result == math_remainder_128(value))
{
  return value % 128ULL;
}

uint8_t first_byte_matches_mixed_width_math(uint64_t value)
  post(result == math_uleb_first_byte(value))
{
  uint8_t byte = value & 0x7f;
  if (value >= 128)
    byte |= 0x80;
  return byte;
}

uint8_t second_digit_matches_nested_math(uint64_t value)
  post(result == math_uleb_second_digit(value))
{
  return (value >> 7) & 0x7f;
}

// CHECK-DAG: Verified: shift_matches_math_division
// CHECK-DAG: Verified: mask_matches_math_remainder
// CHECK-DAG: Verified: machine_division_matches_math
// CHECK-DAG: Verified: machine_remainder_matches_math
// CHECK-DAG: Verified: first_byte_matches_mixed_width_math
// CHECK-DAG: Verified: second_digit_matches_nested_math
