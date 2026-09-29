// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: not %cpp-verify --int-encoding=bitvector %s 2>&1 \
// RUN:   | FileCheck %s --check-prefix=VERIFY
// RUN: %cpp-verify --int-encoding=bitvector --lower-only --dump-ir=1,2,3 %s \
// RUN:   2>&1 | FileCheck %s --check-prefix=IR
//
// A mathematical spec value never wraps into a C++ type. Materializing one in
// ghost or proof code, passing one to a machine parameter, or casting one
// explicitly must prove that it fits. Implicit conversions inside contracts
// keep the value mathematical.

spec int scaled(int x) { return x * 1000; }
spec unsigned below(unsigned x) { return x - 5; }
spec int negated(int x) { return -x - 1; }
constexpr int next(int v) { return v + 1; }
constexpr short next_short(short v) { return v + 1; }
spec int scaled_next(int x) { return next(x * 1000); }

void ghost_in_range(int x)
  pre(x >= 0 && x <= 1000)
{
  ghost {
    int value = scaled(x);
    contract_assert(value == x * 1000);
  }
}

void ghost_out_of_range(int x)
  pre(x >= 0)
{
  ghost { int value = scaled(x); }
}

// 3000000000 would wrap to a negative int.
void ghost_no_wrap(int x)
  pre(x == 3000000)
{
  ghost {
    int value = scaled(x);
    contract_assert(value < 0);
  }
}

void ghost_negative_unsigned(unsigned x)
  pre(x == 3)
{
  ghost {
    unsigned value = below(x);
    contract_assert(value == 4294967294u);
  }
}

void ghost_machine_arithmetic(int x)
  pre(x >= 0 && x <= 1000)
{
  ghost {
    int value = scaled(x) + 1;
    contract_assert(value == x * 1000 + 1);
  }
}

proof void proof_in_range(int x)
  pre(x >= 0 && x <= 1000)
{
  int value = scaled(x);
  contract_assert(value >= 0);
}

proof void proof_out_of_range(int x)
  pre(x >= 0)
{
  int value = scaled(x);
}

void constexpr_argument_in_range(int x)
  pre(x >= 0 && x <= 1000)
  post(next(scaled(x)) == x * 1000 + 1)
{
}

void constexpr_argument_out_of_range(int x)
  pre(x >= 0)
  post(next(scaled(x)) > 0)
{
}

int constexpr_short_parameter(int x)
  pre(x >= 0 && x <= 30)
  post(result == next_short(scaled(x)))
{
  return x * 1000 + 1;
}

int constexpr_short_parameter_out_of_range(int x)
  pre(x >= 0 && x <= 40)
  post(result == next_short(scaled(x)))
{
  return x * 1000 + 1;
}

void spec_through_constexpr(int x)
  pre(x >= 0 && x <= 1000)
  post(scaled_next(x) == x * 1000 + 1)
{
}

void spec_through_constexpr_out_of_range(int x)
  pre(x >= 0)
  post(scaled_next(x) != 5)
{
}

int contract_exact(int x)
  pre(x >= 0 && x <= 1000)
  post(result == scaled(x))
{
  return x * 1000;
}

// The implicit int-to-long conversion does not reduce modulo 2^32.
long contract_implicit_widening(int x)
  pre(x >= 0 && x <= 3000000)
  post(result == scaled(x))
{
  return (long)x * 1000;
}

long contract_mixed_arithmetic(int x, long n)
  pre(x >= 0 && x <= 3000000 && n >= 0 && n <= 10)
  post(result == scaled(x) + n)
  post(result == 1 + scaled(x) + n - 1)
{
  return (long)x * 1000 + n;
}

// The int sum 1 + scaled(x) is mathematical, so widening it cannot wrap.
long contract_mixed_widening(int x)
  pre(x >= 0 && x <= 3000000)
  post(result == 1 + scaled(x))
  post(result == (long)(1 + scaled(x)))
{
  return (long)x * 1000 + 1;
}

// Converting that sum to int, however, must fit.
int contract_mixed_narrowing(int x)
  pre(x >= 0 && x <= 3000000)
  post(result == 0 || result == (int)(1 + scaled(x)))
  post(result == (int)(1 + scaled(x)))
{
  return x <= 2147483 ? x * 1000 + 1 : 0;
}

unsigned contract_implicit_unsigned(int x)
  pre(x >= 0 && x <= 10)
  post(result > negated(x))
{
  return 0;
}

unsigned contract_mixed_order(unsigned count)
  pre(count <= 5)
  post(result <= scaled((int)count) && scaled((int)count) >= result)
{
  return count;
}

long contract_conditional(int x, bool choose)
  pre(x >= 0 && x <= 3000000)
  post(result == (choose ? scaled(x) + 1 : 1))
{
  return choose ? (long)x * 1000 + 1 : 1;
}

int contract_explicit_cast(int x)
  pre(x >= 0 && x <= 2000000)
  post(result == (int)scaled(x))
{
  return x * 1000;
}

int contract_explicit_cast_out_of_range(int x)
  pre(x >= 0)
  post(result == (int)scaled(x))
{
  return 0;
}

long contract_explicit_long(int x)
  pre(x >= 0 && x <= 3000000)
  post(result == (long)scaled(x))
{
  return (long)x * 1000;
}

unsigned contract_explicit_unsigned_negative(int x)
  pre(x >= 0 && x <= 10)
  post(result > (unsigned)negated(x))
{
  return 0;
}

int contract_shift(int x)
  pre(x >= 0 && x <= 1000)
  post(result == (scaled(x) << 1))
{
  return x * 2000;
}

int contract_bitwise_out_of_range(int x)
  pre(x >= 0)
  post(result == (scaled(x) & 255))
{
  return 0;
}

int contract_division_by_zero(int x, int y)
  pre(x >= 0 && x <= 10)
  post(result == scaled(x) / y)
{
  return 0;
}

// VERIFY-DAG: Verified: ghost_in_range
// VERIFY-DAG: error: verification failed: ghost_out_of_range [{{.*}}::overflow@
// VERIFY-DAG: error: verification failed: ghost_no_wrap [{{.*}}::overflow@
// VERIFY-DAG: error: verification failed: ghost_negative_unsigned [{{.*}}::overflow@
// VERIFY-DAG: Verified: ghost_machine_arithmetic
// VERIFY-DAG: Verified: proof_in_range
// VERIFY-DAG: error: verification failed: proof_out_of_range [{{.*}}::overflow@
// VERIFY-DAG: Verified: constexpr_argument_in_range
// VERIFY-DAG: error: verification failed: constexpr_argument_out_of_range [{{.*}}::overflow@
// VERIFY-DAG: Verified: constexpr_short_parameter [
// VERIFY-DAG: error: verification failed: constexpr_short_parameter_out_of_range [{{.*}}::overflow@
// VERIFY-DAG: Verified: spec_through_constexpr [
// VERIFY-DAG: error: verification failed: spec_through_constexpr_out_of_range [{{.*}}::overflow@
// VERIFY-DAG: Verified: contract_exact
// VERIFY-DAG: Verified: contract_implicit_widening
// VERIFY-DAG: Verified: contract_mixed_arithmetic
// VERIFY-DAG: Verified: contract_mixed_widening
// VERIFY-DAG: error: verification failed: contract_mixed_narrowing [{{.*}}::overflow@
// VERIFY-DAG: Verified: contract_implicit_unsigned
// VERIFY-DAG: Verified: contract_mixed_order
// VERIFY-DAG: Verified: contract_conditional
// VERIFY-DAG: Verified: contract_explicit_cast [
// VERIFY-DAG: error: verification failed: contract_explicit_cast_out_of_range [{{.*}}::overflow@
// VERIFY-DAG: Verified: contract_explicit_long
// VERIFY-DAG: error: verification failed: contract_explicit_unsigned_negative [{{.*}}::overflow@
// VERIFY-DAG: Verified: contract_shift
// VERIFY-DAG: error: verification failed: contract_bitwise_out_of_range [{{.*}}::overflow@
// VERIFY-DAG: error: verification failed: contract_division_by_zero [{{.*}}::division-by-zero@

// Layer 1: the ghost materialization is an explicit conversion.
// IR-LABEL: fn ghost_in_range
// IR: ghost
// IR-NEXT: assign value
// IR-NEXT: cast
// IR-NEXT: *
// Layer 2: its fits-in-range check precedes the assignment.
// IR-LABEL: passive ghost_in_range
// IR: assert overflow
// IR: >=
// IR: -2147483648
// IR: <=
// IR: 2147483647
// IR: ==
// IR-NEXT: value_1
// IR-NEXT: cast
// Layer 3: the check compares the exact mathematical value.
// IR-LABEL: vc ghost_in_range
// IR: overflow
// IR: -2147483648 : int
// IR: 2147483647 : int
