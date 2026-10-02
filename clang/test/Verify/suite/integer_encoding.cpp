// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only -Wno-shift-count-negative %s
// RUN: %cpp-verify --int-encoding=integer --lower-only --dump-ir=4 %s 2>&1 | FileCheck %s --check-prefix=INT
// RUN: %cpp-verify --lower-only --dump-ir=4 %s 2>&1 | FileCheck %s --check-prefix=AUTO
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefixes=VERIFY,WRAP,DECIDED,MODEL
// RUN: not %cpp-verify --int-encoding=bitvector %s 2>&1 | FileCheck %s --check-prefixes=VERIFY,WRAP,DECIDED,MODEL
// RUN: not %cpp-verify --int-encoding=integer %s 2>&1 | FileCheck %s --check-prefixes=VERIFY,WRAP,UNDECIDED,MODEL

// All encodings are exact, so decided verdicts and counterexamples agree.

unsigned wrap_add(unsigned x)
  post(result == (x == 4294967295u ? 0u : x + 1u))
{
  return x + 1u;
}
// INT: (and (>= x_0 0) (< x_0 4294967296))
// INT: (mod (+ x_0 1) 4294967296)
// AUTO: (and (>= x_0 0) (< x_0 4294967296))
// AUTO: (mod (+ x_0 1) 4294967296)

int signed_add(int x)
  pre(x < 2147483647)
  post(result > x)
{
  return x + 1;
}
// INT: (and (>= x_0 (- 2147483648)) (< x_0 2147483648))
// INT: (- (mod (+ (+ x_0 1) 2147483648) 4294967296) 2147483648)

unsigned char narrow(unsigned x)
  post(result == (x & 255u))
{
  return (unsigned char)x;
}
// A mask is arithmetic modulo 2^8; so is a truncation, which is stated as the
// value itself when that already fits.
// INT: (and (>= __result_1 0) (< __result_1 256))
// INT: (= __result_1 (ite (and (>= x_0 0) (< x_0 256)) x_0 (mod x_0 256)))
// INT: (= __result_1 (mod x_0 256))

unsigned combine(unsigned x, unsigned y)
  post(result == (y | x))
{
  return x | y;
}
// Forced integers name each operand's bits by a defined bit-vector; auto
// encodes this query with bit-vectors instead.
// INT: (=> (and (>= y_0 0) (< y_0 4294967296)) (= (bv2int bits!0) y_0))
// INT-NEXT: (=> (and (>= x_0 0) (< x_0 4294967296)) (= (bv2int bits!1) x_0))
// INT: (bv2int (bvor bits!1 bits!0))
// AUTO-NOT: bits!
// AUTO: (not (= __result_1 (bvor x_0 y_0)))

unsigned shift_by_signed(unsigned x, int s)
  pre(s >= 0 && s < 32)
  post(result <= x)
{
  return x >> s;
}
// The amount is read in its own signed sort.
// INT: (and (>= s_0 (- 2147483648)) (< s_0 2147483648))
// INT: (bvslt bits!1 #x00000000)
// INT: (bvlshr bits!0 bits!1)
// AUTO: (not (= __result_1 (bvlshr x_0 s_0)))

unsigned bad_wrap(unsigned x)
  post(result > x)
{
  return x + 1u;
}

int bad_negative_shift(int x)
  pre(x == 1)
  post(result == result)
{
  return x << -1;
}
// A negative shift count is undefined; its constant check folds to false.
// INT: (a!2 (and false

// WRAP-DAG: Verified: wrap_add
// VERIFY-DAG: Verified: signed_add
// VERIFY-DAG: Verified: narrow
// VERIFY-DAG: Verified: combine
// DECIDED-DAG: Verified: shift_by_signed
// UNDECIDED-DAG: {{Verified|Unresolved}}: shift_by_signed
// VERIFY-DAG: error: verification failed: bad_wrap
// MODEL-DAG: x [ssa=x_0] [type=u32] = 4294967295;
// VERIFY-DAG: error: verification failed: bad_negative_shift
// MODEL-DAG: x [ssa=x_0] [type=i32] = 1;
