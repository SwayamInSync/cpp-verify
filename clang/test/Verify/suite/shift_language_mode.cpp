// RUN: not %cpp-verify %s -- -std=c++17 2>&1 | FileCheck %s --check-prefixes=CHECK,CXX17
// RUN: not %cpp-verify %s -- -std=c++20 2>&1 | FileCheck %s --check-prefixes=CHECK,CXX20
//
// C++20 defines a signed left shift as the value congruent to E1 * 2^E2
// modulo 2^N. Before C++20 it is undefined for a negative E1 and for a value
// that does not fit the corresponding unsigned type. In both, the amount must
// lie below the width, and a right shift of a negative value is arithmetic
// (before C++20 implementation-defined, and arithmetic in Clang).

int neg_shift()
  cppverify::post(cppverify::result == -2)
{
  int m = -1;
  return m << 1;
}
// CXX17-DAG: error: verification failed: neg_shift [shift]
// CXX20-DAG: Verified: neg_shift [backend=z3]

int neg_shift_assign()
  cppverify::post(cppverify::result == -8)
{
  int m = -2;
  m <<= 2;
  return m;
}
// CXX17-DAG: error: verification failed: neg_shift_assign [shift]
// CXX20-DAG: Verified: neg_shift_assign [backend=z3]

// 2 * 2^31 fits neither int nor unsigned int; modulo 2^32 it is 0.
int past_unsigned(int x)
  cppverify::pre(x == 2)
  cppverify::post(cppverify::result == 0)
{
  return x << 31;
}
// CXX17-DAG: error: verification failed: past_unsigned [shift]
// CXX20-DAG: Verified: past_unsigned [backend=z3]

// A contract is C++ too.
int doubled(int x)
  cppverify::pre(x == -4)
  cppverify::post(cppverify::result == (x << 1))
{
  return x * 2;
}
// CXX17-DAG: error: verification failed: doubled [shift]
// CXX20-DAG: Verified: doubled [backend=z3]

// 2^31 fits unsigned int, so this is INT_MIN in both.
int sign_bit()
  cppverify::post(cppverify::result == -2147483647 - 1)
{
  int one = 1;
  return one << 31;
}
// CHECK-DAG: Verified: sign_bit [backend=z3]

int too_far(int x, int k)
  cppverify::pre(x == 1 && k == 32)
{
  return x << k;
}
// CHECK-DAG: error: verification failed: too_far [shift]

int neg_right()
  cppverify::post(cppverify::result == -2)
{
  int m = -3;
  return m >> 1;
}
// CHECK-DAG: Verified: neg_right [backend=z3]

unsigned wraps()
  cppverify::post(cppverify::result == 0)
{
  unsigned u = 2;
  return u << 31;
}
// CHECK-DAG: Verified: wraps [backend=z3]
