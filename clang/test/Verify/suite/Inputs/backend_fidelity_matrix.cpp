cppverify::spec bool valid(int *pointer, int count) {
  return true;
}

cppverify::spec int math_quotient(int value, int divisor) {
  return value / divisor;
}

cppverify::spec int math_remainder(int value, int divisor) {
  return value % divisor;
}

cppverify::spec int math_increment(int value) {
  return value + 1;
}

cppverify::spec int triangular(int value) cppverify::decreases(value) {
  if (value <= 0)
    return 0;
  return value + triangular(value - 1);
}

cppverify::spec int prefix_sum(int *pointer, int count) cppverify::decreases(count) {
  if (count <= 0)
    return 0;
  return prefix_sum(pointer, count - 1) + pointer[count - 1];
}

struct BoundedValue {
  int value;
  cppverify::type_invariant(value >= 0 && value <= 10);
};

int boolean_control(bool flag)
  cppverify::post(cppverify::result == (flag ? 1 : 2))
{
  return flag ? 1 : 2;
}

int boolean_literal_invalid()
  cppverify::post(false)
{
  return 0;
}

int mathematical_specs()
  cppverify::post(math_quotient(-7, 3) == -2)
  cppverify::post(math_remainder(-7, 3) == -1)
  cppverify::post(math_quotient(7, 0) == 0)
  cppverify::post(math_remainder(7, 0) == 7)
{
  return 0;
}

cppverify::proof void spec_boundary(int value)
  cppverify::pre(value == 5)
{
  int next = math_increment(value);
  cppverify::check(next == 6);
}

cppverify::proof void recursive_spec()
  cppverify::post(triangular(3) == 6)
{
  cppverify::reveal_with_fuel(triangular, 4);
}

unsigned bitvector_operations(unsigned value)
  cppverify::pre(value == 0x80000001U)
  cppverify::post(cppverify::result == value)
{
  cppverify::check((value & 0xffU) == 1U);
  cppverify::check((value | 2U) == 0x80000003U);
  cppverify::check((value ^ 1U) == 0x80000000U);
  cppverify::check((~value) == 0x7ffffffeU);
  cppverify::check((value << 1U) == 2U);
  cppverify::check((value >> 1U) == 0x40000000U);
  return value;
}

unsigned char narrowing_conversion(unsigned value)
  cppverify::pre(value == 257U)
  cppverify::post(cppverify::result == 1U)
{
  return value;
}

unsigned widening_conversion(unsigned char value)
  cppverify::pre(value == 255U)
  cppverify::post(cppverify::result == 255U)
{
  return value;
}

int quantified_valid()
  cppverify::post(cppverify::forall(i, 0, 0, i < 0))
  cppverify::post(cppverify::exists(j, 0, 1, j == 0))
{
  return 0;
}

int quantified_invalid()
  cppverify::post(cppverify::forall(i, 0, 4, i < 3))
{
  return 0;
}

int heap_read(int *pointer)
  cppverify::pre(pointer != nullptr)
  cppverify::post(cppverify::result == *pointer)
{
  return *pointer;
}

void heap_write(int *pointer)
  cppverify::pre(pointer != nullptr)
  cppverify::modifies(*pointer)
  cppverify::post(*pointer == 9)
{
  *pointer = 9;
}

void heap_write_invalid(int *pointer)
  cppverify::pre(pointer != nullptr)
  cppverify::modifies(*pointer)
  cppverify::post(*pointer == 10)
{
  *pointer = 9;
}

int default_nonalias(int *left, int *right)
  cppverify::pre(left != nullptr && right != nullptr)
  cppverify::post(cppverify::result == 1)
{
  return left != right;
}

int bounded_read(int *pointer)
  cppverify::pre(valid(pointer, 1))
  cppverify::post(cppverify::result == pointer[0])
{
  return pointer[0];
}

int bounded_read_invalid(int *pointer)
  cppverify::pre(valid(pointer, 1))
  cppverify::post(cppverify::result == cppverify::result)
{
  return pointer[1];
}

int type_invariant_read(BoundedValue value)
  cppverify::post(cppverify::result >= 0 && cppverify::result <= 10)
{
  return value.value;
}

int safe_add(int value)
  cppverify::pre(value == 5)
  cppverify::post(cppverify::result == 6)
{
  return value + 1;
}

int overflow_add(int value)
  cppverify::pre(value == 2147483647)
  cppverify::post(cppverify::result == cppverify::result)
{
  return value + 1;
}

int overflow_subtract(int value)
  cppverify::pre(value == (-2147483647 - 1))
  cppverify::post(cppverify::result == cppverify::result)
{
  return value - 1;
}

int overflow_multiply(int value)
  cppverify::pre(value == 1073741824)
  cppverify::post(cppverify::result == cppverify::result)
{
  return value * 2;
}

int overflow_negate(int value)
  cppverify::pre(value == (-2147483647 - 1))
  cppverify::post(cppverify::result == cppverify::result)
{
  return -value;
}

int division_by_zero(int value)
  cppverify::pre(value == 0)
  cppverify::post(cppverify::result == cppverify::result)
{
  return 1 / value;
}

int division_overflow(int value)
  cppverify::pre(value == (-2147483647 - 1))
  cppverify::post(cppverify::result == cppverify::result)
{
  return value / -1;
}

int complete_loop()
  cppverify::post(cppverify::result == 1)
{
  int value = 0;
  while (value < 1)
    cppverify::invariant(value >= 0 && value <= 1)
    cppverify::decreases(1 - value)
  {
    value = value + 1;
  }
  return value;
}

void heap_spec_read(int *pointer)
  cppverify::pre(valid(pointer, 2))
  cppverify::pre(pointer[0] >= -100 && pointer[0] <= 100)
  cppverify::pre(pointer[1] >= -100 && pointer[1] <= 100)
  cppverify::modifies(*pointer)
  cppverify::post(prefix_sum(pointer, 2) ==
       cppverify::old(prefix_sum(pointer, 2)) - cppverify::old(pointer[0]))
{
  cppverify::ghost { cppverify::reveal_with_fuel(prefix_sum, 3); }
  pointer[0] = 0;
}

cppverify::spec int scaled_value(int value) { return 3 * value; }

int hidden_spec_true(int value)
  cppverify::pre(value >= -100 && value <= 100)
  cppverify::post(cppverify::result == scaled_value(value))
{
  cppverify::ghost { cppverify::hide(scaled_value); }
  return 3 * value;
}

int hidden_spec_invalid(int value)
  cppverify::pre(value >= -100 && value <= 100)
  cppverify::post(cppverify::result == scaled_value(value))
{
  cppverify::ghost { cppverify::hide(scaled_value); }
  return value == 17 ? 0 : 3 * value;
}

void heap_spec_read_invalid(int *pointer)
  cppverify::pre(valid(pointer, 2))
  cppverify::pre(pointer[0] >= -100 && pointer[0] <= 100)
  cppverify::pre(pointer[1] >= -100 && pointer[1] <= 100)
  cppverify::modifies(*pointer)
  cppverify::post(prefix_sum(pointer, 2) == cppverify::old(prefix_sum(pointer, 2)))
{
  cppverify::ghost { cppverify::reveal_with_fuel(prefix_sum, 3); }
  pointer[0] = 0;
}
