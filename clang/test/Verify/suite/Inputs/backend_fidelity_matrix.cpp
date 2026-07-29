spec bool valid(int *pointer, int count) {
  return true;
}

spec int math_quotient(int value, int divisor) {
  return value / divisor;
}

spec int math_remainder(int value, int divisor) {
  return value % divisor;
}

spec int math_increment(int value) {
  return value + 1;
}

spec int triangular(int value) decreases(value) {
  if (value <= 0)
    return 0;
  return value + triangular(value - 1);
}

struct BoundedValue {
  int value;
  type_invariant(value >= 0 && value <= 10);
};

int boolean_control(bool flag)
  post(result == (flag ? 1 : 2))
{
  return flag ? 1 : 2;
}

int boolean_literal_invalid()
  post(false)
{
  return 0;
}

int mathematical_specs()
  post(math_quotient(-7, 3) == -2)
  post(math_remainder(-7, 3) == -1)
  post(math_quotient(7, 0) == 0)
  post(math_remainder(7, 0) == 7)
{
  return 0;
}

int spec_boundary(int value)
  pre(value == 5)
  post(result == 6)
{
  return math_increment(value);
}

proof void recursive_spec()
  post(triangular(3) == 6)
{
  reveal_with_fuel(triangular, 4);
}

unsigned bitvector_operations(unsigned value)
  pre(value == 0x80000001U)
  post(result == value)
{
  contract_assert((value & 0xffU) == 1U);
  contract_assert((value | 2U) == 0x80000003U);
  contract_assert((value ^ 1U) == 0x80000000U);
  contract_assert((~value) == 0x7ffffffeU);
  contract_assert((value << 1U) == 2U);
  contract_assert((value >> 1U) == 0x40000000U);
  return value;
}

unsigned char narrowing_conversion(unsigned value)
  pre(value == 257U)
  post(result == 1U)
{
  return value;
}

unsigned widening_conversion(unsigned char value)
  pre(value == 255U)
  post(result == 255U)
{
  return value;
}

int quantified_valid()
  post(forall(i, 0, 0, i < 0))
  post(exists(j, 0, 1, j == 0))
{
  return 0;
}

int quantified_invalid()
  post(forall(i, 0, 4, i < 3))
{
  return 0;
}

int heap_read(int *pointer)
  pre(pointer != nullptr)
  post(result == *pointer)
{
  return *pointer;
}

void heap_write(int *pointer)
  pre(pointer != nullptr)
  modifies(*pointer)
  post(*pointer == 9)
{
  *pointer = 9;
}

void heap_write_invalid(int *pointer)
  pre(pointer != nullptr)
  modifies(*pointer)
  post(*pointer == 10)
{
  *pointer = 9;
}

int default_nonalias(int *left, int *right)
  pre(left != nullptr && right != nullptr)
  post(result == 1)
{
  return left != right;
}

int bounded_read(int *pointer)
  pre(valid(pointer, 1))
  post(result == pointer[0])
{
  return pointer[0];
}

int bounded_read_invalid(int *pointer)
  pre(valid(pointer, 1))
  post(result == result)
{
  return pointer[1];
}

int type_invariant_read(BoundedValue value)
  post(result >= 0 && result <= 10)
{
  return value.value;
}

int safe_add(int value)
  pre(value == 5)
  post(result == 6)
{
  return value + 1;
}

int overflow_add(int value)
  pre(value == 2147483647)
  post(result == result)
{
  return value + 1;
}

int overflow_subtract(int value)
  pre(value == (-2147483647 - 1))
  post(result == result)
{
  return value - 1;
}

int overflow_multiply(int value)
  pre(value == 1073741824)
  post(result == result)
{
  return value * 2;
}

int overflow_negate(int value)
  pre(value == (-2147483647 - 1))
  post(result == result)
{
  return -value;
}

int division_by_zero(int value)
  pre(value == 0)
  post(result == result)
{
  return 1 / value;
}

int division_overflow(int value)
  pre(value == (-2147483647 - 1))
  post(result == result)
{
  return value / -1;
}

int complete_loop()
  post(result == 1)
{
  int value = 0;
  while (value < 1)
    invariant(value >= 0 && value <= 1)
    decreases(1 - value)
  {
    value = value + 1;
  }
  return value;
}
