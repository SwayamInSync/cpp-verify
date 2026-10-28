// RUN: not %cpp-verify --jobs=1 %s -- -std=c++23 -Wno-unused-value > %t 2>&1
// RUN: FileCheck %s < %t
// RUN: FileCheck %s --check-prefix=SOUND < %t
// RUN: not %cpp-verify --jobs=1 %s -- -std=c++23 -Wno-unused-value -DNDEBUG 2>&1 | FileCheck %s --check-prefix=NDEBUG
// RUN: not %cpp-verify --jobs=1 --backend=bmc --unroll=2 %s -- -std=c++23 -Wno-unused-value 2>&1 | FileCheck %s --check-prefix=BMC
// RUN: %cpp-verify --lower-only --dump-ir=1 %s -- -std=c++23 -Wno-unused-value 2>&1 | FileCheck %s --check-prefix=VCR
//
// assert(c), and every call that does not return (abort, exit,
// std::terminate, __builtin_unreachable, __builtin_trap), must not be
// reached where it ends the program: reaching one is a failure of kind
// unreachable, and the path ends there, so after assert(c) the condition
// holds. With NDEBUG, assert(c) is nothing, as compiled. [[assume(e)]] and
// __builtin_assume(e) make e false undefined, so e is proved, then assumed.
// Every correct function has a wrong twin that must be refuted.
//
// No proof here holds only because no execution reaches its end.
// SOUND-NOT: vacuous

#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <exception>

namespace cv = cppverify;

int checked(int x)
  cv::pre(x > 0)
  cv::post(cv::result == x)
{
  assert(x > 0 && "x must be positive");
  return x;
}
// CHECK-DAG: Verified: checked [backend=z3]
// NDEBUG-DAG: Verified: checked [backend=z3]

int checked_wrong(int x)
  cv::post(cv::result == x)
{
  assert(x > 0 && "x must be positive");
  return x;
}
// CHECK-DAG: :[[@LINE-3]]:3: error: verification failed: checked_wrong [unreachable] {{.*}}[reason=counterexample]
// CHECK-DAG: note: counterexample: {{.*}}x = {{-?[0-9]+}}{{( ->|,|$)}}
// NDEBUG-DAG: Verified: checked_wrong [backend=z3]

// MSVC's assert expands to a || whose right operand calls _wassert, which
// is not marked [[noreturn]].
extern "C" void _wassert(const wchar_t *, const wchar_t *, unsigned);

int msvc_assert(int x)
  cv::post(cv::result > 0)
{
  (void)((!!(x > 0)) || (_wassert(L"x > 0", L"assertions.cpp", 1), 0));
  return x;
}
// CHECK-DAG: :[[@LINE-3]]:{{[0-9]+}}: error: verification failed: msvc_assert [unreachable]{{.*}}[reason=counterexample]

// After assert(c), c holds.
int positive_after(int x)
  cv::pre(x != 0)
  cv::post(cv::result > 0)
{
  assert(x > 0);
  return x;
}
// CHECK-DAG: :[[@LINE-3]]:3: error: verification failed: positive_after [unreachable]{{.*}}[reason=counterexample]
// NDEBUG-DAG: error: verification failed: positive_after [postcondition]{{.*}}[reason=counterexample]

int positive_after_check(int x)
  cv::pre(x > 0)
  cv::post(cv::result > 0)
{
  assert(x > 0);
  return x;
}
// CHECK-DAG: Verified: positive_after_check [backend=z3]

int aborts(int x)
  cv::post(cv::result >= 0)
{
  if (x < 0)
    abort();
  return x;
}
// CHECK-DAG: :[[@LINE-3]]:5: error: verification failed: aborts [unreachable] {{.*}}[reason=counterexample]
// CHECK-DAG: note: counterexample: {{.*}}x = {{-[0-9]+}}{{( ->|,|$)}}

int aborts_guarded(int x)
  cv::pre(x >= 0)
  cv::post(cv::result >= 0)
{
  if (x < 0)
    abort();
  return x;
}
// CHECK-DAG: Verified: aborts_guarded [backend=z3]

int exits(int code)
  cv::pre(code != 0)
  cv::post(true)
{
  if (code == 0)
    exit(1);
  if (code > 100)
    std::terminate();
  return code;
}
// CHECK-DAG: :[[@LINE-3]]:5: error: verification failed: exits [unreachable] {{.*}}[reason=counterexample]
// CHECK-DAG: note: counterexample: {{.*}}code = {{[0-9]+}}{{( ->|,|$)}}

int classify(int x)
  cv::pre(0 <= x && x < 3)
  cv::post(cv::result == x + 1)
{
  if (x == 0)
    return 1;
  if (x == 1)
    return 2;
  if (x == 2)
    return 3;
  __builtin_unreachable();
}
// CHECK-DAG: Verified: classify [backend=z3]

int classify_wrong(int x)
  cv::pre(0 <= x && x < 4)
  cv::post(cv::result == x + 1)
{
  if (x == 0)
    return 1;
  if (x == 1)
    return 2;
  if (x == 2)
    return 3;
  __builtin_trap();
}
// CHECK-DAG: :[[@LINE-2]]:3: error: verification failed: classify_wrong [unreachable] {{.*}}[reason=counterexample]
// CHECK-DAG: note: counterexample: {{.*}}x = 3{{( ->|,|$)}}

// An assumption is proved where it stands, then holds.
int assumed(int x)
  cv::pre(x > 5)
  cv::post(cv::result > 1)
{
  [[assume(x > 0)]];
  __builtin_assume(x > 1);
  return x;
}
// CHECK-DAG: Verified: assumed [backend=z3]

int assumed_wrong(int x)
  cv::post(cv::result > 0)
{
  [[assume(x > 0)]];
  return x;
}
// CHECK-DAG: :[[@LINE-3]]:{{[0-9]+}}: error: verification failed: assumed_wrong [assertion] {{.*}}[reason=counterexample]
// CHECK-DAG: note: counterexample: {{.*}}x = {{-?[0-9]+}}{{( ->|,|$)}}

// A discarded value is computed, with its checks; the operands of a
// discarded ||, &&, or ?: run on their paths.
int discarded(int x)
  cv::pre(x == 2147483647)
  cv::post(cv::result == 0)
{
  x + 1;
  return 0;
}
// CHECK-DAG: :[[@LINE-3]]:{{[0-9]+}}: error: verification failed: discarded [overflow]{{.*}}[reason=counterexample]

int or_else(int x)
  cv::post(cv::result > 0)
{
  x > 0 || (abort(), 0);
  return x;
}
// CHECK-DAG: :[[@LINE-3]]:{{[0-9]+}}: error: verification failed: or_else [unreachable]{{.*}}[reason=counterexample]

int or_else_guarded(int x)
  cv::pre(x > 0)
  cv::post(cv::result > 0)
{
  x > 0 || (abort(), 0);
  x <= 0 ? abort() : (void)0;
  (void)(x > 0 && x < 2147483647);
  return x;
}
// CHECK-DAG: Verified: or_else_guarded [backend=z3]

// A constexpr helper without a contract is lifted; its assert(c) is a
// requirement of each call, checked there, as its undefined operations are.
constexpr int half(int x) {
  assert(x % 2 == 0);
  return x / 2;
}

constexpr int quarter(int x) { return half(half(x)); }

int use_half(int x)
  cv::pre(-1000 < x && x < 1000 && x % 2 == 0)
  cv::post(2 * cv::result == x)
{
  return half(x);
}
// CHECK-DAG: Verified: use_half [backend=z3]

int use_half_wrong(int x)
  cv::pre(-1000 < x && x < 1000)
  cv::post(true)
{
  return half(x);
}
// CHECK-DAG: :[[@LINE-2]]:{{[0-9]+}}: error: verification failed: use_half_wrong [unreachable]{{.*}}[reason=counterexample]

int use_quarter_wrong(int x)
  cv::pre(-1000 < x && x < 1000 && x % 4 == 2)
  cv::post(true)
{
  return quarter(x);
}
// CHECK-DAG: :[[@LINE-2]]:{{[0-9]+}}: error: verification failed: use_quarter_wrong [unreachable]{{.*}}[reason=counterexample]
// NDEBUG-DAG: Verified: use_quarter_wrong [backend=z3]

// The requirement holds on the helper's path to the call that does not
// return, and the helper has a value wherever it returns.
constexpr int checked_div(int a, int b) {
  if (b == 0)
    abort();
  return a / b;
}

constexpr int must_be_positive(int x) {
  if (x > 0)
    return x;
  abort();
}

int use_div(int a, int b)
  cv::pre(-1000 < a && a < 1000 && b > 0)
  cv::post(cv::result == a / b)
{
  return checked_div(a, b);
}
// CHECK-DAG: Verified: use_div [backend=z3]

int use_div_wrong(int a, int b)
  cv::pre(-1000 < a && a < 1000)
  cv::post(true)
{
  return checked_div(a, b);
}
// CHECK-DAG: :[[@LINE-2]]:{{[0-9]+}}: error: verification failed: use_div_wrong [unreachable] {{.*}}[reason=counterexample]
// CHECK-DAG: note: counterexample: {{.*}}b = 0{{( ->|,|$)}}

int use_positive(int x)
  cv::pre(x > 0)
  cv::post(cv::result == x)
{
  return must_be_positive(x);
}
// CHECK-DAG: Verified: use_positive [backend=z3]

// LLVM 23.1.3's MathExtras.h, verbatim but for the contracts.
constexpr uint64_t divideCeil(uint64_t Numerator, uint64_t Denominator) {
  assert(Denominator && "Division by zero");
  uint64_t Bias = (Numerator != 0);
  return (Numerator - Bias) / Denominator + Bias;
}

constexpr uint64_t alignTo(uint64_t Value, uint64_t Align)
  cv::pre(Align != 0 && Value <= UINT64_MAX - Align)
  cv::post(cv::result % Align == 0)
  cv::post(Value <= cv::result && cv::result < Value + Align)
{
  assert(Align != 0u && "Align can't be 0.");
  uint64_t CeilDiv = divideCeil(Value, Align);
  return CeilDiv * Align;
}
// CHECK-DAG: Verified: alignTo [backend=z3]

uint64_t alignTo_zero(uint64_t Value)
  cv::post(true)
{
  return alignTo(Value, 0);
}
// CHECK-DAG: :[[@LINE-2]]:{{[0-9]+}}: error: verification failed: alignTo_zero [precondition]{{.*}}[reason=counterexample]

inline constexpr uint64_t maxUIntN(uint64_t N)
  cv::pre(N <= 64)
  cv::post(N == 64 || cv::result + 1 == ((__int128)1 << N))
{
  assert(N <= 64 && "integer width out of range");

  // uint64_t(1) << 64 is undefined behavior, so we can't do
  //   (uint64_t(1) << N) - 1
  // without checking first that N != 64.  But this works and doesn't have a
  // branch for N != 0.
  // Unfortunately, shifting a uint64_t right by 64 bit is undefined
  // behavior, so the condition on N == 0 is necessary. Fortunately, most
  // optimizers do not emit branches for this check.
  if (N == 0)
    return 0;
  return UINT64_MAX >> (64 - N);
}
// CHECK-DAG: Verified: maxUIntN [backend=z3]

inline int64_t SignExtend64(uint64_t X, unsigned B)
  cv::pre(B <= 64)
  cv::post(B == 0 || B == 64 ||
           (-((__int128)1 << (B - 1)) <= cv::result &&
            cv::result < ((__int128)1 << (B - 1))))
{
  assert(B <= 64 && "Bit width out of range.");
  if (B == 0)
    return 0;
  return int64_t(X << (64 - B)) >> (64 - B);
}
// CHECK-DAG: Verified: SignExtend64 [backend=z3]

int64_t SignExtend64_wide(uint64_t X, unsigned B)
  cv::post(true)
{
  assert(B <= 64 && "Bit width out of range.");
  if (B == 0)
    return 0;
  return int64_t(X << (64 - B)) >> (64 - B);
}
// CHECK-DAG: :[[@LINE-5]]:3: error: verification failed: SignExtend64_wide [unreachable] {{.*}}[reason=counterexample]
// CHECK-DAG: note: counterexample: {{.*}}B = {{[0-9]+}}{{( ->|,|$)}}
// NDEBUG-DAG: error: verification failed: SignExtend64_wide [shift]{{.*}}[reason=counterexample]

// BMC: Verified: checked [backend=bmc, bound=0]
// BMC: error: verification failed: checked_wrong [unreachable]
// BMC: error: verification failed: aborts [unreachable]

// VCR-LABEL: fn aborts
// VCR:         {{^ +}}if{{$}}
// VCR-NEXT:      <
// VCR-NEXT:        x
// VCR-NEXT:        0
// VCR-NEXT:      assert unreachable
// VCR-NEXT:        false
// VCR-NEXT:      assume
// VCR-NEXT:        false
