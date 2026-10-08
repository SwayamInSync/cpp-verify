// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY

cppverify::spec int math_identity(int x) {
  return x;
}

cppverify::spec int math_increment(int x) {
  return x + 1;
}

int safe_signed_add(int x)
  cppverify::pre(x >= -100 && x <= 100)
  cppverify::post(cppverify::result == x + 1)
{
  return x + 1;
}

int safe_machine_code_with_spec_contract(int x)
  cppverify::pre(x >= -100 && x <= 100)
  cppverify::post(math_identity(cppverify::result) == x + 1)
{
  return x + 1;
}

cppverify::proof void safe_machine_code_after_spec_result(int x)
  cppverify::pre(x >= -100 && x <= 100)
{
  int value = math_identity(x) + 1;
  cppverify::check(value == x + 1);
}

cppverify::proof void safe_unbounded_spec_identity(int x)
{
  int value = math_identity(x);
  cppverify::check(value == x);
}

unsigned safe_unsigned_wrap(unsigned x)
  cppverify::pre(x == 0xffffffffU)
  cppverify::post(cppverify::result == 0U)
{
  return x + 1U;
}

int safe_guarded_division(int x)
  cppverify::post(cppverify::result == 0)
{
  return x == 0 ? 0 : 0 / x;
}

int safe_short_circuit_load(int *p)
  cppverify::post(cppverify::result == 0)
{
  if (p != nullptr && *p > 0)
    return 0;
  return 0;
}

int unsafe_null_load(int *p)
  cppverify::post(cppverify::result == cppverify::result)
{
  return *p;
}

void unsafe_null_store(int *p)
  cppverify::modifies(*p)
{
  *p = 1;
}

int unsafe_division_by_zero(int x)
  cppverify::post(cppverify::result == cppverify::result)
{
  return 1 / x;
}

int unsafe_remainder_by_zero(int x)
  cppverify::post(cppverify::result == cppverify::result)
{
  return 1 % x;
}

int unsafe_signed_add(int x)
  cppverify::pre(x == 2147483647)
{
  return x + 1;
}

int unsafe_overflow_with_spec_contract(int x)
  cppverify::pre(x == 2147483647)
  cppverify::post(math_identity(cppverify::result) == cppverify::result)
{
  return x + 1;
}

cppverify::proof void unsafe_overflow_after_spec_result(int x)
  cppverify::pre(x == 2147483647)
{
  int value = math_identity(x) + 1;
  cppverify::check(value < 0);
}

cppverify::proof void unsafe_overflow_after_spec_initialization(int x)
  cppverify::pre(x == 2147483647)
{
  int value = math_identity(x);
  int next = value + 1;
  cppverify::check(next < 0);
}

cppverify::proof void unsafe_overflow_after_spec_assignment(int x)
  cppverify::pre(x == 2147483647)
{
  int value = 0;
  value = math_identity(x);
  int next = value + 1;
  cppverify::check(next < 0);
}

// The mathematical result 2^31 has no int representation; it must not wrap.
cppverify::proof void invalid_out_of_range_spec_result(int x)
  cppverify::pre(x == 2147483647)
{
  int value = math_increment(x);
  cppverify::check(value < 0);
}

int unsafe_signed_subtract(int x)
  cppverify::pre(x == -2147483647 - 1)
{
  return x - 1;
}

int unsafe_signed_multiply(int x)
  cppverify::pre(x == 1073741824)
{
  return x * 2;
}

int unsafe_signed_negation(int x)
  cppverify::pre(x == -2147483647 - 1)
{
  return -x;
}

int unsafe_min_division(int x)
  cppverify::pre(x == -2147483647 - 1)
{
  return x / -1;
}

int unsafe_min_remainder(int x)
  cppverify::pre(x == -2147483647 - 1)
{
  return x % -1;
}

// VERIFY-DAG: Verified: safe_signed_add
// VERIFY-DAG: Verified: safe_machine_code_with_spec_contract
// VERIFY-DAG: Verified: safe_machine_code_after_spec_result
// VERIFY-DAG: Verified: safe_unbounded_spec_identity
// VERIFY-DAG: Verified: safe_unsigned_wrap
// VERIFY-DAG: Verified: safe_guarded_division
// VERIFY-DAG: Verified: safe_short_circuit_load
// VERIFY-DAG: error: verification failed: unsafe_null_load
// VERIFY-DAG: error: verification failed: unsafe_null_store
// VERIFY-DAG: error: verification failed: unsafe_division_by_zero
// VERIFY-DAG: error: verification failed: unsafe_remainder_by_zero
// VERIFY-DAG: error: verification failed: unsafe_signed_add
// VERIFY-DAG: error: verification failed: unsafe_overflow_with_spec_contract
// VERIFY-DAG: error: verification failed: unsafe_overflow_after_spec_result
// VERIFY-DAG: error: verification failed: unsafe_overflow_after_spec_initialization
// VERIFY-DAG: error: verification failed: unsafe_overflow_after_spec_assignment
// VERIFY-DAG: error: verification failed: invalid_out_of_range_spec_result [{{.*}}::overflow@
// VERIFY-DAG: error: verification failed: unsafe_signed_subtract
// VERIFY-DAG: error: verification failed: unsafe_signed_multiply
// VERIFY-DAG: error: verification failed: unsafe_signed_negation
// VERIFY-DAG: error: verification failed: unsafe_min_division
// VERIFY-DAG: error: verification failed: unsafe_min_remainder
