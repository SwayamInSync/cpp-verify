namespace cppverify_uleb128_portfolio {

typedef __UINT64_TYPE__ uint64_t;
typedef __UINT8_TYPE__ uint8_t;

cppverify::spec bool valid(uint8_t *pointer, int count) {
  return true;
}

cppverify::spec int uleb_length(uint64_t value) {
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

unsigned encode_uleb128_length(uint64_t value, uint8_t *buffer)
  cppverify::pre(valid(buffer, 10))
  cppverify::modifies(*buffer)
  cppverify::post(cppverify::result == uleb_length(cppverify::old(value)))
  cppverify::post(cppverify::result >= 1 && cppverify::result <= 10)
{
  uint64_t original = value;
  unsigned count = 0;
  do {
    uint8_t byte = value & 0x7f;
    value >>= 7;
    count += 1;
    if (value != 0)
      byte |= 0x80;
    buffer[count - 1] = byte;
  } while (value != 0)
    cppverify::invariant(count >= 1 && count <= 10)
    cppverify::invariant(count <= uleb_length(original))
    cppverify::invariant(value ==
              (count == 10 ? 0ULL : original >> (7 * count)))
    cppverify::invariant((value == 0) == (count == uleb_length(original)))
    cppverify::decreases(value);
  return count;
}

} // namespace cppverify_uleb128_portfolio

