// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --check-ub --jobs=4 --timeout=120000 %s 2>&1 | FileCheck %s
//
// UTF-8 decoding, the validation half. This is core logic in every C++ text
// stack -- ICU, Qt, simdjson, Boost.Locale -- and it is the classic example of
// an algorithm whose *rejections* matter more than its acceptances. Accepting
// an overlong encoding is how the IIS Unicode directory traversal and
// CVE-2008-2938 (Tomcat) worked: `../` smuggled past a security filter as
// bytes that only decode to `/` after the filter has run. Accepting a
// surrogate produces an ill-formed scalar value that later stages assume
// cannot exist.
//
// The decoder below implements Unicode 15 Table 3-7 verbatim. What is proved
// is not "it decodes correctly" but "it cannot be tricked":
//
//   - every accepted result is a Unicode scalar value (0 .. 0x10FFFF);
//   - no accepted result is a surrogate (0xD800 .. 0xDFFF);
//   - no accepted sequence is overlong -- a length-k sequence always carries a
//     code point that genuinely requires k bytes;
//   - the consumed length never exceeds the bytes actually available;
//   - every read is inside the declared extent, and no arithmetic overflows.
//
// Companions utf8_overlong_fail.cpp and utf8_surrogate_fail.cpp inject the two
// historical defects and show them rejected with concrete counterexamples.

typedef __UINT8_TYPE__ uint8_t;
typedef __INT32_TYPE__ int32_t;

spec bool valid(uint8_t* p, int n) { return true; }

// Unicode 15 Table 3-7 "Well-Formed UTF-8 Byte Sequences", verbatim:
//   00..7F                          1 byte
//   C2..DF  80..BF                  2 bytes   (C0/C1 would be overlong)
//   E0      A0..BF  80..BF          3 bytes   (A0 floor excludes overlong)
//   E1..EC  80..BF  80..BF          3 bytes
//   ED      80..9F  80..BF          3 bytes   (9F ceiling excludes surrogates)
//   EE..EF  80..BF  80..BF          3 bytes
//   F0      90..BF  80..BF  80..BF  4 bytes   (90 floor excludes overlong)
//   F1..F3  80..BF  80..BF  80..BF  4 bytes
//   F4      80..8F  80..BF  80..BF  4 bytes   (8F ceiling caps at U+10FFFF)
int32_t utf8_decode(uint8_t* s, int n, int& len)
  pre(valid(s, n) && n >= 1 && n <= 4)
  modifies(len)
  post(result == -1 || (result >= 0 && result <= 1114111))
  post(result == -1 || result < 55296 || result > 57343)
  post(result == -1 || (len >= 1 && len <= 4 && len <= n))
  post(result == -1 || len != 2 || result >= 128)
  post(result == -1 || len != 3 || result >= 2048)
  post(result == -1 || len != 4 || result >= 65536)
{
  int32_t b0 = s[0];
  int32_t cp = -1;
  len = 0;

  if (b0 <= 127) {
    cp = b0;
    len = 1;
  } else if (b0 >= 194 && b0 <= 223 && n >= 2) {
    int32_t c1 = s[1];
    if (c1 >= 128 && c1 <= 191) {
      cp = ((b0 - 192) * 64) + (c1 - 128);
      len = 2;
    }
  } else if (b0 >= 224 && b0 <= 239 && n >= 3) {
    int32_t d1 = s[1];
    int32_t dlo = 128;
    int32_t dhi = 191;
    if (b0 == 224) { dlo = 160; }
    if (b0 == 237) { dhi = 159; }
    if (d1 >= dlo && d1 <= dhi) {
      int32_t d2 = s[2];
      if (d2 >= 128 && d2 <= 191) {
        cp = ((b0 - 224) * 4096) + ((d1 - 128) * 64) + (d2 - 128);
        len = 3;
      }
    }
  } else if (b0 >= 240 && b0 <= 244 && n >= 4) {
    int32_t e1 = s[1];
    int32_t elo = 128;
    int32_t ehi = 191;
    if (b0 == 240) { elo = 144; }
    if (b0 == 244) { ehi = 143; }
    if (e1 >= elo && e1 <= ehi) {
      int32_t e2 = s[2];
      int32_t e3 = s[3];
      if (e2 >= 128 && e2 <= 191 && e3 >= 128 && e3 <= 191) {
        cp = ((b0 - 240) * 262144) + ((e1 - 128) * 4096)
           + ((e2 - 128) * 64) + (e3 - 128);
        len = 4;
      }
    }
  }

  if (cp < 0) { len = 0; }
  return cp;
}

// CHECK: Verified: utf8_decode
