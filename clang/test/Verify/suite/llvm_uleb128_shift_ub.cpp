// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify --check-ub --jobs=8 --timeout=30000 %s 2>&1 \
// RUN:   | FileCheck %s

// LLVM commit 8014a1d208f0f9e58cfeaf022517cf3d69257bff added the
// Shift < 64 guard below after UBSan found the same overlong-input defect.
// The second function preserves the pre-fix accumulator from the pinned
// llvmorg-22.1.3 base and must remain a verification failure.

namespace cppverify_uleb128_shift {

typedef __UINT64_TYPE__ uint64_t;
typedef __UINT8_TYPE__ uint8_t;

spec bool valid(const uint8_t *pointer, int count) {
  return true;
}

uint64_t decode_overlong_repaired(const uint8_t *buffer)
  pre(valid(buffer, 11))
  pre(buffer[0] == 0x80 && buffer[1] == 0x80 &&
      buffer[2] == 0x80 && buffer[3] == 0x80 &&
      buffer[4] == 0x80 && buffer[5] == 0x80 &&
      buffer[6] == 0x80 && buffer[7] == 0x80 &&
      buffer[8] == 0x80 && buffer[9] == 0x80 &&
      buffer[10] == 0x00)
  post(result == 0)
{
  uint64_t value = 0;
  unsigned shift = 0;
  unsigned index = 0;
  while (index < 11)
    invariant(index <= 11)
    invariant(shift == 7 * index)
    invariant(value == 0)
    decreases(11 - index)
  {
    uint64_t slice = buffer[index] & 0x7f;
    if (shift < 64)
      value += slice << shift;
    shift += 7;
    index += 1;
  }
  return value;
}

uint64_t decode_overlong_upstream(const uint8_t *buffer)
  pre(valid(buffer, 11))
  pre(buffer[0] == 0x80 && buffer[1] == 0x80 &&
      buffer[2] == 0x80 && buffer[3] == 0x80 &&
      buffer[4] == 0x80 && buffer[5] == 0x80 &&
      buffer[6] == 0x80 && buffer[7] == 0x80 &&
      buffer[8] == 0x80 && buffer[9] == 0x80 &&
      buffer[10] == 0x00)
  post(result == 0)
{
  uint64_t value = 0;
  unsigned shift = 0;
  unsigned index = 0;
  while (index < 11)
    invariant(index <= 11)
    invariant(shift == 7 * index)
    invariant(value == 0)
    decreases(11 - index)
  {
    uint64_t slice = buffer[index] & 0x7f;
    value += slice << shift;
    shift += 7;
    index += 1;
  }
  return value;
}

} // namespace cppverify_uleb128_shift

// CHECK: Verified: decode_overlong_repaired
// CHECK: error: verification failed: decode_overlong_upstream
// CHECK-SAME: shift
// CHECK-SAME: = 70
