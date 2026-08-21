// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --check-ub --jobs=8 --timeout=30000 %s 2>&1 | FileCheck %s

// Flagship case study derived from llvm/Support/LEB128.h at LLVM commit
// 007f107aaf5ff2b111fc107ed23e6e88bcc0d9e9.
//
// The executable arithmetic and do-while order are preserved. The encoder is
// specified independently with mathematical base-128 division and remainder;
// explicit lemmas connect LLVM's shifts and masks to that model. The proof
// extraction specializes PadTo to zero and replaces the mutable *p++ cursor
// with buffer[count - 1] so valid(buffer, 10) remains attached to its
// allocation base.

namespace cppverify_uleb128 {

typedef __UINT64_TYPE__ uint64_t;
typedef __UINT8_TYPE__ uint8_t;

spec bool valid(uint8_t *pointer, int count) {
  return true;
}

spec bool valid(const uint8_t *pointer, unsigned count) {
  return true;
}

spec int uleb_length(uint64_t value) {
  if (value < 128ULL)
    return 1;
  if (value < 16384ULL)
    return 2;
  if (value < 2097152ULL)
    return 3;
  if (value < 268435456ULL)
    return 4;
  if (value < 34359738368ULL)
    return 5;
  if (value < 4398046511104ULL)
    return 6;
  if (value < 562949953421312ULL)
    return 7;
  if (value < 72057594037927936ULL)
    return 8;
  if (value < 9223372036854775808ULL)
    return 9;
  return 10;
}

spec unsigned uleb_digit_math(uint64_t value, unsigned index) {
  if (index == 0)
    return value % 128;
  if (index == 1)
    return (value / 128) % 128;
  if (index == 2)
    return (value / 16384) % 128;
  if (index == 3)
    return (value / 2097152) % 128;
  if (index == 4)
    return (value / 268435456) % 128;
  if (index == 5)
    return (value / 34359738368ULL) % 128;
  if (index == 6)
    return (value / 4398046511104ULL) % 128;
  if (index == 7)
    return (value / 562949953421312ULL) % 128;
  if (index == 8)
    return (value / 72057594037927936ULL) % 128;
  if (index == 9)
    return (value / 9223372036854775808ULL) % 128;
  return 0;
}

spec unsigned uleb_byte_math_0(uint64_t value) {
  return (value % 128) + (value >= 128 ? 128 : 0);
}

spec unsigned uleb_byte_math_1(uint64_t value) {
  return ((value / 128) % 128) + (value >= 16384 ? 128 : 0);
}

spec unsigned uleb_byte_math_2(uint64_t value) {
  return ((value / 16384) % 128) + (value >= 2097152 ? 128 : 0);
}

spec unsigned uleb_byte_math_3(uint64_t value) {
  return ((value / 2097152) % 128) + (value >= 268435456 ? 128 : 0);
}

spec unsigned uleb_byte_math_4(uint64_t value) {
  return ((value / 268435456) % 128) +
         (value >= 34359738368ULL ? 128 : 0);
}

spec unsigned uleb_byte_math_5(uint64_t value) {
  return ((value / 34359738368ULL) % 128) +
         (value >= 4398046511104ULL ? 128 : 0);
}

spec unsigned uleb_byte_math_6(uint64_t value) {
  return ((value / 4398046511104ULL) % 128) +
         (value >= 562949953421312ULL ? 128 : 0);
}

spec unsigned uleb_byte_math_7(uint64_t value) {
  return ((value / 562949953421312ULL) % 128) +
         (value >= 72057594037927936ULL ? 128 : 0);
}

spec unsigned uleb_byte_math_8(uint64_t value) {
  return ((value / 72057594037927936ULL) % 128) +
         (value >= 9223372036854775808ULL ? 128 : 0);
}

spec unsigned uleb_byte_math_9(uint64_t value) {
  return (value / 9223372036854775808ULL) % 128;
}

spec unsigned uleb_byte_math(uint64_t value, unsigned index) {
  if (index == 0)
    return uleb_byte_math_0(value);
  if (index == 1)
    return uleb_byte_math_1(value);
  if (index == 2)
    return uleb_byte_math_2(value);
  if (index == 3)
    return uleb_byte_math_3(value);
  if (index == 4)
    return uleb_byte_math_4(value);
  if (index == 5)
    return uleb_byte_math_5(value);
  if (index == 6)
    return uleb_byte_math_6(value);
  if (index == 7)
    return uleb_byte_math_7(value);
  if (index == 8)
    return uleb_byte_math_8(value);
  if (index == 9)
    return uleb_byte_math_9(value);
  return 0;
}

constexpr uint8_t uleb_byte_machine(uint64_t value, unsigned index) {
  if (index >= 10)
    return 0;
  uint64_t shifted = value >> (7 * index);
  uint8_t byte = shifted & 0x7f;
  shifted >>= 7;
  if (shifted != 0)
    byte |= 0x80;
  return byte;
}

proof void lemma_machine_byte_0(uint64_t value)
  post(uleb_byte_machine(value, 0) == uleb_byte_math_0(value))
{
}

proof void lemma_machine_byte_1(uint64_t value)
  post(uleb_byte_machine(value, 1) == uleb_byte_math_1(value))
{
}

proof void lemma_machine_byte_2(uint64_t value)
  post(uleb_byte_machine(value, 2) == uleb_byte_math_2(value))
{
}

proof void lemma_machine_byte_3(uint64_t value)
  post(uleb_byte_machine(value, 3) == uleb_byte_math_3(value))
{
}

proof void lemma_machine_byte_4(uint64_t value)
  post(uleb_byte_machine(value, 4) == uleb_byte_math_4(value))
{
}

proof void lemma_machine_byte_5(uint64_t value)
  post(uleb_byte_machine(value, 5) == uleb_byte_math_5(value))
{
}

proof void lemma_machine_byte_6(uint64_t value)
  post(uleb_byte_machine(value, 6) == uleb_byte_math_6(value))
{
}

proof void lemma_machine_byte_7(uint64_t value)
  post(uleb_byte_machine(value, 7) == uleb_byte_math_7(value))
{
}

proof void lemma_machine_byte_8(uint64_t value)
  post(uleb_byte_machine(value, 8) == uleb_byte_math_8(value))
{
}

proof void lemma_machine_byte_9(uint64_t value)
  post(uleb_byte_machine(value, 9) == uleb_byte_math_9(value))
{
}

proof void lemma_machine_byte_matches_math(uint64_t value, unsigned index)
  pre(index < 10)
  post(uleb_byte_machine(value, index) == uleb_byte_math(value, index))
{
  if (index == 0)
    lemma_machine_byte_0(value);
  else if (index == 1)
    lemma_machine_byte_1(value);
  else if (index == 2)
    lemma_machine_byte_2(value);
  else if (index == 3)
    lemma_machine_byte_3(value);
  else if (index == 4)
    lemma_machine_byte_4(value);
  else if (index == 5)
    lemma_machine_byte_5(value);
  else if (index == 6)
    lemma_machine_byte_6(value);
  else if (index == 7)
    lemma_machine_byte_7(value);
  else if (index == 8)
    lemma_machine_byte_8(value);
  else
    lemma_machine_byte_9(value);
}

constexpr uint64_t uleb_prefix_value(uint64_t value, unsigned count) {
  if (count == 0)
    return 0;
  if (count >= 10)
    return value;
  unsigned bits = 7 * count;
  return value & ((1ULL << bits) - 1ULL);
}

unsigned encode_uleb128(uint64_t value, uint8_t *buffer)
  pre(valid(buffer, 10))
  modifies(buffer[0], buffer[1], buffer[2], buffer[3], buffer[4],
           buffer[5], buffer[6], buffer[7], buffer[8], buffer[9])
  post(result == uleb_length(old(value)))
  post(result >= 1 && result <= 10)
  post(result <= 0 || buffer[0] == uleb_byte_math(old(value), 0))
  post(result <= 1 || buffer[1] == uleb_byte_math(old(value), 1))
  post(result <= 2 || buffer[2] == uleb_byte_math(old(value), 2))
  post(result <= 3 || buffer[3] == uleb_byte_math(old(value), 3))
  post(result <= 4 || buffer[4] == uleb_byte_math(old(value), 4))
  post(result <= 5 || buffer[5] == uleb_byte_math(old(value), 5))
  post(result <= 6 || buffer[6] == uleb_byte_math(old(value), 6))
  post(result <= 7 || buffer[7] == uleb_byte_math(old(value), 7))
  post(result <= 8 || buffer[8] == uleb_byte_math(old(value), 8))
  post(result <= 9 || buffer[9] == uleb_byte_math(old(value), 9))
  post(result > 0 || buffer[0] == old(buffer[0]))
  post(result > 1 || buffer[1] == old(buffer[1]))
  post(result > 2 || buffer[2] == old(buffer[2]))
  post(result > 3 || buffer[3] == old(buffer[3]))
  post(result > 4 || buffer[4] == old(buffer[4]))
  post(result > 5 || buffer[5] == old(buffer[5]))
  post(result > 6 || buffer[6] == old(buffer[6]))
  post(result > 7 || buffer[7] == old(buffer[7]))
  post(result > 8 || buffer[8] == old(buffer[8]))
  post(result > 9 || buffer[9] == old(buffer[9]))
{
  uint64_t original = value;
  unsigned count = 0;
  do {
    uint8_t byte = value & 0x7f;
    value >>= 7;
    count = count + 1;
    if (value != 0)
      byte |= 0x80;
    buffer[count - 1] = byte;
  } while (value != 0)
    invariant(count >= 1 && count <= 10)
    invariant(count <= uleb_length(original))
    invariant(value ==
              (count == 10 ? 0ULL : original >> (7 * count)))
    invariant((value == 0) == (count == uleb_length(original)))
    invariant(count <= 0 || buffer[0] == uleb_byte_machine(original, 0))
    invariant(count <= 1 || buffer[1] == uleb_byte_machine(original, 1))
    invariant(count <= 2 || buffer[2] == uleb_byte_machine(original, 2))
    invariant(count <= 3 || buffer[3] == uleb_byte_machine(original, 3))
    invariant(count <= 4 || buffer[4] == uleb_byte_machine(original, 4))
    invariant(count <= 5 || buffer[5] == uleb_byte_machine(original, 5))
    invariant(count <= 6 || buffer[6] == uleb_byte_machine(original, 6))
    invariant(count <= 7 || buffer[7] == uleb_byte_machine(original, 7))
    invariant(count <= 8 || buffer[8] == uleb_byte_machine(original, 8))
    invariant(count <= 9 || buffer[9] == uleb_byte_machine(original, 9))
    invariant(count > 0 || buffer[0] == old(buffer[0]))
    invariant(count > 1 || buffer[1] == old(buffer[1]))
    invariant(count > 2 || buffer[2] == old(buffer[2]))
    invariant(count > 3 || buffer[3] == old(buffer[3]))
    invariant(count > 4 || buffer[4] == old(buffer[4]))
    invariant(count > 5 || buffer[5] == old(buffer[5]))
    invariant(count > 6 || buffer[6] == old(buffer[6]))
    invariant(count > 7 || buffer[7] == old(buffer[7]))
    invariant(count > 8 || buffer[8] == old(buffer[8]))
    invariant(count > 9 || buffer[9] == old(buffer[9]))
    decreases(value);
  ghost {
    lemma_machine_byte_0(original);
    lemma_machine_byte_1(original);
    lemma_machine_byte_2(original);
    lemma_machine_byte_3(original);
    lemma_machine_byte_4(original);
    lemma_machine_byte_5(original);
    lemma_machine_byte_6(original);
    lemma_machine_byte_7(original);
    lemma_machine_byte_8(original);
    lemma_machine_byte_9(original);
  }
  return count;
}

uint64_t decode_uleb128_canonical(const uint8_t *buffer, unsigned length,
                                  uint64_t expected, unsigned *consumed)
  pre(valid(buffer, length))
  pre(consumed != nullptr)
  pre(length == uleb_length(expected))
  pre(length <= 0 || buffer[0] == uleb_byte_machine(expected, 0))
  pre(length <= 1 || buffer[1] == uleb_byte_machine(expected, 1))
  pre(length <= 2 || buffer[2] == uleb_byte_machine(expected, 2))
  pre(length <= 3 || buffer[3] == uleb_byte_machine(expected, 3))
  pre(length <= 4 || buffer[4] == uleb_byte_machine(expected, 4))
  pre(length <= 5 || buffer[5] == uleb_byte_machine(expected, 5))
  pre(length <= 6 || buffer[6] == uleb_byte_machine(expected, 6))
  pre(length <= 7 || buffer[7] == uleb_byte_machine(expected, 7))
  pre(length <= 8 || buffer[8] == uleb_byte_machine(expected, 8))
  pre(length <= 9 || buffer[9] == uleb_byte_machine(expected, 9))
  modifies(*consumed)
  post(result == expected)
  post(*consumed == length)
{
  uint64_t value = 0;
  unsigned shift = 0;
  unsigned index = 0;
  do {
    uint64_t slice = buffer[index] & 0x7f;
    value += slice << shift;
    shift += 7;
    index += 1;
  } while (buffer[index - 1] >= 128)
    invariant(index >= 1 && index <= length)
    invariant(shift == 7 * index)
    invariant(value == uleb_prefix_value(expected, index))
    invariant((buffer[index - 1] >= 128) == (index < length))
    decreases(length - index);
  *consumed = index;
  return value;
}

uint64_t roundtrip_uleb128(uint64_t input, uint8_t *buffer,
                           unsigned *consumed)
  pre(valid(buffer, 10))
  pre(consumed != nullptr)
  modifies(buffer[0], buffer[1], buffer[2], buffer[3], buffer[4],
           buffer[5], buffer[6], buffer[7], buffer[8], buffer[9], *consumed)
  post(result == input)
  post(*consumed == uleb_length(input))
{
  unsigned length = encode_uleb128(input, buffer);
  ghost {
    lemma_machine_byte_0(input);
    lemma_machine_byte_1(input);
    lemma_machine_byte_2(input);
    lemma_machine_byte_3(input);
    lemma_machine_byte_4(input);
    lemma_machine_byte_5(input);
    lemma_machine_byte_6(input);
    lemma_machine_byte_7(input);
    lemma_machine_byte_8(input);
    lemma_machine_byte_9(input);
  }
  return decode_uleb128_canonical(buffer, length, input, consumed);
}

} // namespace cppverify_uleb128

// CHECK-DAG: Verified: encode_uleb128
// CHECK-DAG: Verified: lemma_machine_byte_matches_math
// CHECK-DAG: Verified: decode_uleb128_canonical
// CHECK-DAG: Verified: roundtrip_uleb128
