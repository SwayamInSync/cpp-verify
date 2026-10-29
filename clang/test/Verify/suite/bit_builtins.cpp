// RUN: not %cpp-verify --jobs=1 %s -- 2>&1 | FileCheck %s --check-prefixes=CHECK,BITS
// RUN: not %cpp-verify --jobs=1 --int-encoding=integer --function=l* \
// RUN:   --function=t* --function=c* --function=p* --function=f* --function=v* \
// RUN:   --function=spec_zero --function=asserts %s -- 2>&1 | FileCheck %s
// RUN: not %cpp-verify --jobs=1 --function=lz_zero --diagnostics-format=json %s -- 2>/dev/null | FileCheck %s --check-prefix=JSON
//
// GCC's bit-counting and byte-swapping builtins are their exact definitions
// over the operand's bits. __builtin_clz and __builtin_ctz of 0 are
// undefined: a builtin-argument check where the call is evaluated. In a spec,
// which is total, they count Width zeros there, as C++20's std::countl_zero.
// A static_assert with a message is a declaration with no effect.

namespace cv = cppverify;

int lz(unsigned x)
  cv::pre(x != 0)
  cv::post(0 <= cv::result && cv::result < 32)
  cv::post(x >= 0x80000000u ? cv::result == 0 : cv::result > 0)
{
  return __builtin_clz(x);
}
// CHECK-DAG: Verified: lz [backend=z3]

int lz_zero(unsigned x)
  cv::post(cv::result >= 0)
{
  return __builtin_clz(x);
}
// CHECK-DAG: bit_builtins.cpp:[[@LINE-2]]:10: error: verification failed: lz_zero [builtin-argument]
// CHECK-DAG: bit_builtins.cpp:[[@LINE-3]]:10: note: counterexample: x = 0
// JSON: "obligation":{"id":"{{.*}}::builtin-argument@[[#@LINE-4]]:3","kind":"builtin-argument","source":{"column":10,"end_column":26,"end_line":[[#@LINE-4]],

int tz_zero(unsigned long long x)
  cv::pre(x < 1000)
  cv::post(cv::result >= 0)
{
  return x == 0 ? 64 : __builtin_ctzll(x) + __builtin_ctzll(x - x);
}
// CHECK-DAG: bit_builtins.cpp:[[@LINE-2]]:45: error: verification failed: tz_zero [builtin-argument]

// The argument a contract gives a builtin must be one it is defined for: a
// verified body checks its postcondition where it returns.
int checked_contract(unsigned x)
  cv::post(cv::result == __builtin_clz(x))
{
  return __builtin_clz(x | 1u) + (x & 1u ? 0 : 0) - (x == 0 ? 0 : 0);
}
// CHECK-DAG: bit_builtins.cpp:[[@LINE-4]]:26: error: verification failed: checked_contract [builtin-argument]

// A lifted helper's check is shown where the clause calls the helper.
constexpr int lz_of(unsigned v) { return __builtin_clz(v); }

int lz_post(unsigned x)
  cv::post(cv::result == lz_of(x))
{
  return x == 0 ? 32 : __builtin_clz(x);
}
// CHECK-DAG: bit_builtins.cpp:[[@LINE-4]]:23: error: verification failed: lz_post [builtin-argument]

int tz(unsigned long long x)
  cv::pre(x != 0)
  cv::post(0 <= cv::result && cv::result < 64)
{
  return __builtin_ctzll(x);
}
// CHECK-DAG: Verified: tz [backend=z3]

int pop(unsigned x)
  cv::post(0 <= cv::result && cv::result <= 32)
  cv::post(x == 0 || cv::result > 0)
{
  return __builtin_popcount(x);
}
// CHECK-DAG: Verified: pop [backend=z3]

int pop_wrong(unsigned x)
  cv::post(cv::result < 32)
{
  return __builtin_popcount(x);
}
// CHECK-DAG: verification failed: pop_wrong [postcondition]
// CHECK-DAG: note: counterexample: x = 4294967295, result = 32

unsigned swap(unsigned x)
  cv::post(cv::result == ((x & 0xffu) << 24 | (x & 0xff00u) << 8 |
                          (x >> 8 & 0xff00u) | x >> 24))
{
  return __builtin_bswap32(x);
}
// The integer encoding gives each bitwise term an int2bv, and this
// comparison of 32 of them with shifts took longer than the test should.
// BITS-DAG: Verified: swap [backend=z3]

int first(int x)
  cv::post(x == 0 ? cv::result == 0 : 1 <= cv::result && cv::result <= 32)
{
  return __builtin_ffs(x);
}
// CHECK-DAG: Verified: first [backend=z3]

int par(unsigned x)
  cv::post(cv::result == __builtin_popcount(x) % 2)
{
  return __builtin_parity(x);
}
// CHECK-DAG: Verified: par [backend=z3]

cv::spec int leading(unsigned x) { return __builtin_clz(x); }

void spec_zero()
  cv::post(true)
{
  cv::check(leading(0u) == 32);
}
// CHECK-DAG: Verified: spec_zero [backend=z3]

// Each variant at the ends of its width and at a value of mixed bits.
void values()
  cv::post(true)
{
  cv::check(__builtin_clz(1u) == 31 && __builtin_clz(0x80000000u) == 0);
  cv::check(__builtin_clz(0x00f0f0f0u) == 8);
  cv::check(__builtin_clzl(1ul) == 63 && __builtin_clzll(0x8000000000000000ull) == 0);
  cv::check(__builtin_ctz(0x80000000u) == 31 && __builtin_ctz(0x00f0f0f0u) == 4);
  cv::check(__builtin_ctzl(1ul) == 0 && __builtin_ctzll(0x8000000000000000ull) == 63);
  cv::check(__builtin_popcount(0xffffffffu) == 32 && __builtin_popcount(0x00f0f0f0u) == 12);
  cv::check(__builtin_popcountl(0ul) == 0 && __builtin_popcountll(0xf0f0f0f0f0f0f0f0ull) == 32);
  cv::check(__builtin_parity(0x00f0f0f1u) == 1 && __builtin_parityll(3ull) == 0);
  cv::check(__builtin_ffs(0) == 0 && __builtin_ffs(-2147483647 - 1) == 32);
  cv::check(__builtin_ffsll(0x100ll) == 9 && __builtin_ffsl(1l) == 1);
  cv::check(__builtin_bswap16((unsigned short)0x1234) == 0x3412);
  cv::check(__builtin_bswap32(0x12345678u) == 0x78563412u);
  cv::check(__builtin_bswap64(0x0102030405060708ull) == 0x0807060504030201ull);
}
// CHECK-DAG: Verified: values [backend=z3]

int asserts(int x)
  cv::post(cv::result == x)
{
  static_assert(sizeof(int) == 4, "int is 32 bits");
  return x;
}
// CHECK-DAG: Verified: asserts [backend=z3]
