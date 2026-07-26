// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

constexpr int increment(int value) {
  return value + 1;
}

constexpr int quotient(int value, int divisor) {
  return value / divisor;
}

constexpr int guarded_negate(int value) {
  return value == -2147483648 ? 0 : -value;
}

constexpr unsigned increment_unsigned(unsigned value) {
  return value + 1;
}

constexpr int discarded_increment(int value) {
  int discarded = value + 1;
  return 0;
}

constexpr int guarded_discarded_increment(int value) {
  int discarded = value == 2147483647 ? 0 : value + 1;
  return 0;
}

spec int wrapped_increment(int value) {
  return increment(value);
}

spec unsigned wrapped_increment_unsigned(unsigned value) {
  return increment_unsigned(value);
}

spec unsigned mathematical_increment(unsigned value) {
  return value + 1;
}

int valid_bounded_constexpr(int value)
  pre(value < 2147483647)
  post(increment(value) == value + 1)
{
  return 0;
}

int valid_guarded_constexpr()
  post(guarded_negate(-2147483648) == 0)
{
  return 0;
}

int valid_unsigned_constexpr_wrap()
  post(increment_unsigned(4294967295U) == 0U)
{
  return 0;
}

int valid_nested_constexpr(int value)
  pre(value < 2147483647)
  post(wrapped_increment(value) == value + 1)
{
  return 0;
}

int valid_nested_unsigned_wrap()
  post(wrapped_increment_unsigned(4294967295U) == 0U)
{
  return 0;
}

int valid_guarded_discarded_constexpr()
  post(guarded_discarded_increment(2147483647) == 0)
{
  return 0;
}

int invalid_constexpr_overflow()
  post(increment(2147483647) == -2147483648)
{
  return 0;
}

int invalid_constexpr_divide_by_zero()
  post(quotient(1, 0) == 0)
{
  return 0;
}

int invalid_unbounded_constexpr_call(int value)
  post(result == increment(value))
{
  return increment(value);
}

int invalid_nested_constexpr_overflow()
  post(wrapped_increment(2147483647) == -2147483648)
{
  return 0;
}

int invalid_nested_unsigned_math_bridge(unsigned value)
  pre(value == 4294967295U)
  post(wrapped_increment_unsigned(value) == mathematical_increment(value))
{
  return 0;
}

int invalid_discarded_constexpr_overflow()
  post(discarded_increment(2147483647) == 0)
{
  return 0;
}

// VERIFY-DAG: Verified: valid_bounded_constexpr
// VERIFY-DAG: Verified: valid_guarded_constexpr
// VERIFY-DAG: Verified: valid_unsigned_constexpr_wrap
// VERIFY-DAG: Verified: valid_nested_constexpr
// VERIFY-DAG: Verified: valid_nested_unsigned_wrap
// VERIFY-DAG: Verified: valid_guarded_discarded_constexpr
// VERIFY-DAG: error: verification failed: invalid_constexpr_overflow
// VERIFY-DAG: error: verification failed: invalid_constexpr_divide_by_zero
// VERIFY-DAG: error: verification failed: invalid_unbounded_constexpr_call
// VERIFY-DAG: error: verification failed: invalid_nested_constexpr_overflow
// VERIFY-DAG: error: verification failed: invalid_nested_unsigned_math_bridge
// VERIFY-DAG: error: verification failed: invalid_discarded_constexpr_overflow
