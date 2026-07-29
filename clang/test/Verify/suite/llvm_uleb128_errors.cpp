// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --check-ub --jobs=4 \
// RUN:   --timeout=30000 %s 2>&1 | FileCheck %s

// Deductive checks for the two error predicates in LLVM's decoder. Nested
// const-char** message plumbing is intentionally represented by scalar status.

namespace cppverify_uleb128_errors {

typedef __UINT64_TYPE__ uint64_t;
typedef __UINT8_TYPE__ uint8_t;

spec bool valid(const uint8_t *pointer, int count) {
  return true;
}

unsigned decode_truncated_80(const uint8_t *buffer, unsigned *consumed)
  pre(valid(buffer, 1))
  pre(buffer[0] == 0x80)
  pre(consumed != nullptr)
  modifies(*consumed)
  post(result == 1)
  post(*consumed == 1)
{
  uint64_t value = 0;
  unsigned shift = 0;
  unsigned index = 0;
  unsigned status = 0;
  while (status == 0)
    invariant(status == 0 || status == 1)
    invariant(index <= 1)
    invariant(shift == 7 * index)
    invariant(value == 0)
    invariant(buffer[0] == 0x80)
    invariant(status != 1 || index == 1)
    decreases(2 * (2 - index) + (status == 0 ? 1 : 0))
  {
    if (index == 1) {
      status = 1;
    } else {
      uint8_t byte = buffer[index];
      uint64_t slice = byte & 0x7f;
      if (shift >= 63 &&
          ((shift == 63 && (slice << shift >> shift) != slice) ||
           (shift > 63 && slice != 0))) {
        status = 2;
      } else {
        value += slice << shift;
        shift += 7;
        index += 1;
        if (byte < 128)
          status = 3;
      }
    }
  }
  *consumed = index;
  return status;
}

unsigned decode_tenth_byte_overflow(const uint8_t *buffer,
                                    unsigned *consumed)
  pre(valid(buffer, 10))
  pre(buffer[0] == 0x80 && buffer[1] == 0x80 &&
      buffer[2] == 0x80 && buffer[3] == 0x80 &&
      buffer[4] == 0x80 && buffer[5] == 0x80 &&
      buffer[6] == 0x80 && buffer[7] == 0x80 &&
      buffer[8] == 0x80 && buffer[9] == 0x02)
  pre(consumed != nullptr)
  modifies(*consumed)
  post(result == 2)
  post(*consumed == 9)
{
  uint64_t value = 0;
  unsigned shift = 0;
  unsigned index = 0;
  unsigned status = 0;
  while (status == 0)
    invariant(status == 0 || status == 2)
    invariant(index <= 9)
    invariant(shift == 7 * index)
    invariant(value == 0)
    invariant(buffer[0] == 0x80 && buffer[1] == 0x80 &&
              buffer[2] == 0x80 && buffer[3] == 0x80 &&
              buffer[4] == 0x80 && buffer[5] == 0x80 &&
              buffer[6] == 0x80 && buffer[7] == 0x80 &&
              buffer[8] == 0x80 && buffer[9] == 0x02)
    invariant(status != 2 || index == 9)
    decreases(2 * (10 - index) + (status == 0 ? 1 : 0))
  {
    if (index == 10) {
      status = 1;
    } else {
      uint8_t byte = buffer[index];
      uint64_t slice = byte & 0x7f;
      if (shift >= 63 &&
          ((shift == 63 && (slice << shift >> shift) != slice) ||
           (shift > 63 && slice != 0))) {
        status = 2;
      } else {
        value += slice << shift;
        shift += 7;
        index += 1;
        if (byte < 128)
          status = 3;
      }
    }
  }
  *consumed = index;
  return status;
}

} // namespace cppverify_uleb128_errors

// CHECK-DAG: Verified: decode_truncated_80
// CHECK-DAG: Verified: decode_tenth_byte_overflow
