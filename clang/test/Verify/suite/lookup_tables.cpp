// RUN: not %cpp-verify --jobs=1 %s -- -std=c++20 > %t 2>&1
// RUN: FileCheck %s < %t
// RUN: FileCheck %s --check-prefix=SOUND < %t
// RUN: not %cpp-verify --jobs=1 --backend=bmc --unroll=2 %s -- -std=c++20 2>&1 | FileCheck %s --check-prefix=BMC
// RUN: not %cpp-verify --lower-only --dump-ir=1 %s -- -std=c++20 2>&1 | FileCheck %s --check-prefix=VCR
//
// An element of a constant table, a const or constexpr array with a
// constant initializer (global, static local, or static member) or a string
// literal, is the value its initializer gives it; each index must lie in its
// array. Every correct function has a wrong twin that must be refuted.
//
// No proof here holds only because no execution reaches its end.
// SOUND-NOT: vacuous

#include <cstdint>

namespace cv = cppverify;

// The number of bits set in each nibble.
static const uint8_t NibbleBits[16] = {0, 1, 1, 2, 1, 2, 2, 3,
                                       1, 2, 2, 3, 2, 3, 3, 4};

int popcount8(uint8_t x)
  cv::post(0 <= cv::result && cv::result <= 8)
  cv::post(x != 255 || cv::result == 8)
  cv::post(x != 0 || cv::result == 0)
{
  return NibbleBits[x & 15] + NibbleBits[x >> 4];
}
// CHECK-DAG: Verified: popcount8 [backend=z3]

int popcount8_wrong(uint8_t x)
  cv::post(cv::result <= 7)
{
  return NibbleBits[x & 15] + NibbleBits[x >> 4];
}
// CHECK-DAG: error: verification failed: popcount8_wrong [{{.*}}x [ssa=x_0] [type=u8] = 255{{.*}}[reason=counterexample]

// An index outside the table is undefined.
int nibble_bits(int x)
  cv::post(true)
{
  return NibbleBits[x];
}
// CHECK-DAG: error: verification failed: nibble_bits [{{.*}}::bounds@[[@LINE-2]]:{{.*}}[reason=counterexample]

int nibble_bits_inside(int x)
  cv::pre(0 <= x && x < 16)
  cv::post(0 <= cv::result && cv::result <= 4)
{
  return NibbleBits[x];
}
// CHECK-DAG: Verified: nibble_bits_inside [backend=z3]

// A table declared in a function, two-dimensional, with elements its
// initializer leaves zero.
int add_mod3(int a, int b)
  cv::pre(0 <= a && a < 3 && 0 <= b && b < 3)
  cv::post(cv::result == (a + b) % 3)
{
  static constexpr int Sum[3][3] = {{0, 1, 2}, {1, 2, 0}, {2, 0, 1}};
  return Sum[a][b];
}
// CHECK-DAG: Verified: add_mod3 [backend=z3]

int add_mod3_wrong(int a, int b)
  cv::pre(0 <= a && a < 3 && 0 <= b && b < 3)
  cv::post(cv::result == (a + b) % 3)
{
  static constexpr int Sum[3][3] = {{0, 1, 2}, {1, 2, 0}, {2, 1, 0}};
  return Sum[a][b];
}
// CHECK-DAG: error: verification failed: add_mod3_wrong [{{.*}}a [ssa=a_0] [type=i32] = 2, b [ssa=b_0] [type=i32] = {{1|2}}{{.*}}[reason=counterexample]

int row_outside(int a)
  cv::pre(0 <= a && a < 3)
  cv::post(true)
{
  static constexpr int Sum[3][3] = {{0, 1, 2}, {1, 2, 0}, {2, 0, 1}};
  return Sum[a][3];
}
// CHECK-DAG: error: verification failed: row_outside [{{.*}}::bounds@[[@LINE-2]]:{{.*}}[reason=counterexample]

constexpr int Primes[8] = {2, 3, 5, 7, 11};

int prime_or_zero(int i)
  cv::pre(0 <= i && i < 8)
  cv::post(i < 5 ? cv::result > 1 : cv::result == 0)
{
  return Primes[i];
}
// CHECK-DAG: Verified: prime_or_zero [backend=z3]

// A string literal is a constant array of its characters and a zero.
char hex_digit(int d)
  cv::pre(0 <= d && d < 16)
  cv::post(d < 10 ? cv::result == '0' + d : cv::result == 'a' + d - 10)
{
  return "0123456789abcdef"[d];
}
// CHECK-DAG: Verified: hex_digit [backend=z3]

char hex_digit_wrong(int d)
  cv::pre(0 <= d && d <= 16)
  cv::post(true)
{
  return "0123456789abcdef"[d + 1];
}
// CHECK-DAG: error: verification failed: hex_digit_wrong [{{.*}}::bounds@[[@LINE-2]]:{{.*}}d [ssa=d_0] [type=i32] = 16{{.*}}[reason=counterexample]

// Tables of enumerations and Booleans, and a static member.
enum Kind { Digit, Letter, Other };

struct Ascii {
  static constexpr bool IsUpper[4] = {false, true, true, false};
};

Kind classify(int c)
  cv::pre(0 <= c && c < 4)
  cv::post(cv::result != Other)
{
  static const Kind Classes[4] = {Digit, Letter, Letter, Digit};
  return Ascii::IsUpper[c] ? Letter : Classes[c];
}
// CHECK-DAG: Verified: classify [backend=z3]

// Contracts and ghost code read tables too.
int first_prime()
  cv::post(cv::result == Primes[0])
{
  return 2;
}
// CHECK-DAG: Verified: first_prime [backend=z3]

// A pointer into a constant table is not supported yet.
int via_pointer()
  cv::post(true)
{
  const int *p = Primes;
  return p[1];
}
// CHECK-DAG: lookup_tables.cpp:[[@LINE-3]]:18: error: via_pointer: a pointer into the constant table 'Primes' is unsupported; read its elements by index

// BMC: Verified: popcount8 [backend=bmc, bound=0]
// BMC: error: verification failed: popcount8_wrong

// The read requires its index in bounds; the table is a tree of comparisons.
// VCR-LABEL: fn nibble_bits_inside
// VCR:         return
// VCR-NEXT:      cast
// VCR-NEXT:        ite
// VCR-NEXT:          require bounds
// VCR:             ite
// VCR-NEXT:          <
// VCR-NEXT:            cast
// VCR-NEXT:              x
// VCR-NEXT:            8
