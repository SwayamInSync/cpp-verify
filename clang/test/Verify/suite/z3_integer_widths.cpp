// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

spec unsigned math_u32_max() {
  return 0xffffffffU;
}

spec unsigned long long math_u64_max() {
  return 0xffffffffffffffffULL;
}

int valid_unsigned_literals_in_math_specs()
  post(math_u32_max() == 4294967295ULL)
  post(math_u64_max() == 18446744073709551615ULL)
{
  return 0;
}

unsigned long long valid_u64_literal_bit_pattern()
  post(result == 18446744073709551615ULL)
{
  return 0xffffffffffffffffULL;
}

int valid_i64_high_value(long long x)
  pre(x == 4294967296LL)
  post(x > 2147483647LL)
{
  return 0;
}

int valid_i64_bound(long long x)
  post(x <= 9223372036854775807LL)
{
  return 0;
}

int valid_u64_bound(unsigned long long x)
  post(x <= 18446744073709551615ULL)
{
  return 0;
}

int valid_small_integer_ranges(signed char x, unsigned char y)
  post(x >= -128 && x <= 127)
  post(y >= 0 && y <= 255)
{
  return 0;
}

int valid_narrowing_cast(int x)
  pre(x == 256)
  post((unsigned char)x == 0)
{
  return 0;
}

void valid_i64_heap_store(long long *p)
  pre(p != nullptr)
  modifies(*p)
  post(*p == 4294967296LL)
{
  *p = 4294967296LL;
}

int invalid_i64_collapse(long long x)
  pre(x == 4294967296LL)
  post(x == 0)
{
  return 0;
}

int invalid_i8_upper_bound(signed char x)
  post(x < 127)
{
  return 0;
}

int invalid_u8_upper_bound(unsigned char x)
  post(x < 255)
{
  return 0;
}

void invalid_i64_heap_truncation(long long *p)
  pre(p != nullptr)
  modifies(*p)
  post(*p == 0)
{
  *p = 4294967296LL;
}

// VERIFY-DAG: spec axiom: math_u32_max
// VERIFY-DAG: spec axiom: math_u64_max
// VERIFY-DAG: Verified: valid_unsigned_literals_in_math_specs
// VERIFY-DAG: Verified: valid_u64_literal_bit_pattern
// VERIFY-DAG: Verified: valid_i64_high_value
// VERIFY-DAG: Verified: valid_i64_bound
// VERIFY-DAG: Verified: valid_u64_bound
// VERIFY-DAG: Verified: valid_small_integer_ranges
// VERIFY-DAG: Verified: valid_narrowing_cast
// VERIFY-DAG: Verified: valid_i64_heap_store
// VERIFY-DAG: error: verification failed: invalid_i64_collapse
// VERIFY-DAG: error: verification failed: invalid_i8_upper_bound
// VERIFY-DAG: error: verification failed: invalid_u8_upper_bound
// VERIFY-DAG: error: verification failed: invalid_i64_heap_truncation
