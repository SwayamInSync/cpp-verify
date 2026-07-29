// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify --backend=bmc --unroll=1 --check-ub --jobs=4 \
// RUN:   --timeout=10000 %s 2>&1 | FileCheck %s

namespace cppverify_uleb128_mutation {

typedef __UINT64_TYPE__ uint64_t;
typedef __UINT8_TYPE__ uint8_t;

spec bool valid(uint8_t *pointer, int count) {
  return true;
}

unsigned encode_128(uint8_t *buffer)
  pre(valid(buffer, 10))
  modifies(buffer[0], buffer[1])
  post(result == 2)
  post(buffer[0] == 0x80 && buffer[1] == 0x01)
{
  uint64_t value = 128;
  unsigned count = 0;
  do {
    uint8_t byte = value & 0x7f;
    value >>= 7;
    count += 1;
    if (value != 0)
      byte |= 0x80;
    buffer[count - 1] = byte;
  } while (value != 0);
  return count;
}

unsigned encode_128_missing_continuation(uint8_t *buffer)
  pre(valid(buffer, 10))
  modifies(buffer[0], buffer[1])
  post(result == 2)
  post(buffer[0] == 0x80 && buffer[1] == 0x01)
{
  uint64_t value = 128;
  unsigned count = 0;
  do {
    uint8_t byte = value & 0x7f;
    value >>= 7;
    count += 1;
    buffer[count - 1] = byte;
  } while (value != 0);
  return count;
}

} // namespace cppverify_uleb128_mutation

// CHECK: Verified: encode_128 [backend=bmc, bound=1]
// CHECK: error: verification failed: encode_128_missing_continuation
// CHECK-SAME: buffer
// CHECK-SAME: value=0

