#include "../llvm_uleb128.cpp"
#include "../llvm_uleb128_errors.cpp"
#include "llvm/Support/LEB128.h"

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <limits>

namespace {

constexpr unsigned ExhaustiveLimit = 1U << 20;
constexpr unsigned RandomCases = 1000000;
constexpr uint8_t Sentinel = 0xa5;

uint64_t BoundaryCases = 0;
uint64_t ExhaustiveCases = 0;
uint64_t RandomCaseCount = 0;
uint64_t RandomState = 0x4c4c564d554c4542ULL;

[[noreturn]] void fail(const char *Check, uint64_t Value) {
  std::fprintf(stderr, "failure: %s for value 0x%016llx\n", Check,
               static_cast<unsigned long long>(Value));
  std::abort();
}

uint64_t nextRandom() {
  uint64_t Z = (RandomState += 0x9e3779b97f4a7c15ULL);
  Z = (Z ^ (Z >> 30)) * 0xbf58476d1ce4e5b9ULL;
  Z = (Z ^ (Z >> 27)) * 0x94d049bb133111ebULL;
  return Z ^ (Z >> 31);
}

void checkValue(uint64_t Value) {
  uint8_t Extracted[16];
  uint8_t Upstream[16];
  std::memset(Extracted, Sentinel, sizeof(Extracted));
  std::memset(Upstream, Sentinel, sizeof(Upstream));

  unsigned ExtractedLength =
      cppverify_uleb128::encode_uleb128(Value, Extracted);
  unsigned UpstreamLength = llvm::encodeULEB128(Value, Upstream);
  if (ExtractedLength != UpstreamLength)
    fail("encoded length", Value);
  if (std::memcmp(Extracted, Upstream, ExtractedLength) != 0)
    fail("encoded bytes", Value);

  for (unsigned I = ExtractedLength; I != sizeof(Extracted); ++I) {
    if (Extracted[I] != Sentinel || Upstream[I] != Sentinel)
      fail("unused-byte frame", Value);
  }

  unsigned ExtractedConsumed = 0;
  uint64_t ExtractedDecoded = cppverify_uleb128::decode_uleb128_canonical(
      Extracted, ExtractedLength, Value, &ExtractedConsumed);
  if (ExtractedDecoded != Value || ExtractedConsumed != ExtractedLength)
    fail("extracted decode", Value);

  unsigned UpstreamConsumed = 0;
  const char *Error = "unchanged";
  uint64_t UpstreamDecoded =
      llvm::decodeULEB128(Upstream, &UpstreamConsumed,
                          Upstream + UpstreamLength, &Error);
  if (UpstreamDecoded != Value || UpstreamConsumed != UpstreamLength)
    fail("upstream decode", Value);
  if (std::strcmp(Error, "unchanged") != 0)
    fail("success error output", Value);
}

void checkBoundaries() {
  const uint64_t Fixed[] = {
      0,
      1,
      2,
      0x3f,
      0x40,
      0x7e,
      0x7f,
      0x80,
      0x81,
      0xff,
      0x100,
      0x5555555555555555ULL,
      0xaaaaaaaaaaaaaaaaULL,
      std::numeric_limits<uint64_t>::max() - 1,
      std::numeric_limits<uint64_t>::max(),
  };
  for (uint64_t Value : Fixed) {
    checkValue(Value);
    ++BoundaryCases;
  }

  for (unsigned Shift = 7; Shift <= 63; Shift += 7) {
    uint64_t Threshold = 1ULL << Shift;
    checkValue(Threshold - 1);
    checkValue(Threshold);
    checkValue(Threshold + 1);
    BoundaryCases += 3;
  }
}

void checkMalformed() {
  {
    const uint8_t Bytes[] = {0x80};
    unsigned ExtractedConsumed = 99;
    unsigned ExtractedStatus =
        cppverify_uleb128_errors::decode_truncated_80(
            Bytes, &ExtractedConsumed);
    unsigned Consumed = 99;
    const char *Error = nullptr;
    uint64_t Value =
        llvm::decodeULEB128(Bytes, &Consumed, Bytes + sizeof(Bytes), &Error);
    if (ExtractedStatus != 1 || ExtractedConsumed != Consumed ||
        Value != 0 || Consumed != 1 || Error == nullptr ||
        std::strcmp(Error, "malformed uleb128, extends past end") != 0)
      fail("truncated input", 0);
  }

  {
    const uint8_t Bytes[] = {0x80, 0x80, 0x80, 0x80, 0x80,
                             0x80, 0x80, 0x80, 0x80, 0x02};
    unsigned ExtractedConsumed = 99;
    unsigned ExtractedStatus =
        cppverify_uleb128_errors::decode_tenth_byte_overflow(
            Bytes, &ExtractedConsumed);
    unsigned Consumed = 99;
    const char *Error = nullptr;
    uint64_t Value =
        llvm::decodeULEB128(Bytes, &Consumed, Bytes + sizeof(Bytes), &Error);
    if (ExtractedStatus != 2 || ExtractedConsumed != Consumed ||
        Value != 0 || Consumed != 9 || Error == nullptr ||
        std::strcmp(Error, "uleb128 too big for uint64") != 0)
      fail("overflow input", 0);
  }
}

} // namespace

int main() {
  checkBoundaries();

  for (uint64_t Value = 0; Value != ExhaustiveLimit; ++Value) {
    checkValue(Value);
    ++ExhaustiveCases;
  }

  for (unsigned I = 0; I != RandomCases; ++I) {
    checkValue(nextRandom());
    ++RandomCaseCount;
  }

  checkMalformed();
  std::printf(
      "{\"schema\":\"cppverify.uleb128-native/1\","
      "\"boundary_cases\":%llu,\"exhaustive_cases\":%llu,"
      "\"random_cases\":%llu,\"malformed_cases\":2,"
      "\"seed\":\"0x4c4c564d554c4542\",\"status\":\"passed\"}\n",
      static_cast<unsigned long long>(BoundaryCases),
      static_cast<unsigned long long>(ExhaustiveCases),
      static_cast<unsigned long long>(RandomCaseCount));
  return 0;
}
