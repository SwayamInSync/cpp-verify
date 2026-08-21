// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify --check-ub --timeout=10000 %s 2>&1 | FileCheck %s

typedef __UINT64_TYPE__ uint64_t;
typedef __UINT8_TYPE__ uint8_t;

spec uint64_t math_quotient_128(uint64_t value) {
  return value / 128;
}

spec uint8_t math_remainder_128(uint64_t value) {
  return value % 128;
}

spec unsigned math_uleb_second_digit(uint64_t value) {
  return (value / 128) % 128;
}

uint64_t wrong_quotient(uint64_t value)
  post(result == math_quotient_128(value))
{
  return (value / 128ULL) + 1;
}

uint8_t wrong_remainder(uint64_t value)
  post(result == math_remainder_128(value))
{
  return (value + 1) & 0x7f;
}

uint8_t wrong_second_digit(uint64_t value)
  post(result == math_uleb_second_digit(value))
{
  return ((value >> 7) + 1) & 0x7f;
}

// CHECK-DAG: error: verification failed: wrong_quotient
// CHECK-DAG: error: verification failed: wrong_remainder
// CHECK-DAG: error: verification failed: wrong_second_digit
