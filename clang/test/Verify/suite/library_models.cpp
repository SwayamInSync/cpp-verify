// RUN: not %cpp-verify --jobs=1 %s -- > %t 2>&1
// RUN: FileCheck %s < %t
// RUN: FileCheck %s --check-prefix=QUIET < %t
//
// memcpy, memmove, memset, and memcmp of integers are calls of their models
// in <cppverify.h>, which every proof that uses one trusts; abs is its
// definition, undefined at the minimum. A model is converted only where a
// call uses it, and is not reported.
//
// QUIET-NOT: Trusted:

#include <cstdlib>
#include <cstring>

namespace cv = cppverify;

void copy(int *dst, const int *src, int n)
  cv::pre(cv::valid(dst, n) && cv::valid(src, n) && 0 <= n && n <= 1000)
  cv::modifies(dst[0 : n])
  cv::post(cv::forall(k, 0, n, dst[k] == src[k]))
{
  memcpy(dst, src, n * sizeof(int));
}
// CHECK-DAG: Verified: copy [backend=z3] [trusts=memcpy]

// A caller trusts what its callee's proof trusts.
void copy_twice(int *a, int *b, const int *c)
  cv::pre(cv::valid(a, 4) && cv::valid(b, 4) && cv::valid(c, 4))
  cv::modifies(a[0 : 4], b[0 : 4])
  cv::post(a[3] == c[3] && b[3] == c[3])
{
  copy(a, c, 4);
  std::memcpy(b, a, sizeof(int) * 4);
}
// CHECK-DAG: Verified: copy_twice [backend=z3] [trusts=memcpy]

void shift_left(int *a, int n)
  cv::pre(cv::valid(a, n) && 1 <= n && n <= 1000)
  cv::modifies(a[0 : n])
  cv::post(cv::forall(k, 0, n - 1, a[k] == cv::old(a[k + 1])))
{
  memmove(a, a + 1, (n - 1) * sizeof(int));
}
// CHECK-DAG: Verified: shift_left [backend=z3] [trusts=memmove]

void shift_right(short *a, int n)
  cv::pre(cv::valid(a, n) && 1 <= n && n <= 1000)
  cv::modifies(a[0 : n])
  cv::post(cv::forall(k, 1, n, a[k] == cv::old(a[k - 1])))
{
  memmove(a + 1, a, (n - 1) * sizeof(short));
}
// CHECK-DAG: Verified: shift_right [backend=z3] [trusts=memmove]

enum class Color : unsigned char { Red, Green, Blue };

void copy_colors(Color *dst, const Color *src)
  cv::pre(cv::valid(dst, 3) && cv::valid(src, 3))
  cv::modifies(dst[0 : 3])
  cv::post(dst[2] == src[2])
{
  memcpy(dst, src, 3);
}
// CHECK-DAG: Verified: copy_colors [backend=z3] [trusts=memcpy]

void clear(unsigned *a, int n)
  cv::pre(cv::valid(a, n) && 0 <= n && n <= 1000)
  cv::modifies(a[0 : n])
  cv::post(cv::forall(k, 0, n, a[k] == 0))
{
  memset(a, 0, n * sizeof(unsigned));
}
// CHECK-DAG: Verified: clear [backend=z3] [trusts=memset]

void ones(int *a, int n)
  cv::pre(cv::valid(a, n) && 0 <= n && n <= 1000)
  cv::modifies(a[0 : n])
  cv::post(cv::forall(k, 0, n, a[k] == -1))
{
  memset(a, 0xff, n * sizeof(int));
}
// CHECK-DAG: Verified: ones [backend=z3] [trusts=memset]

void fill_bytes(unsigned char *a, int n, int c)
  cv::pre(cv::valid(a, n) && 0 <= n && n <= 1000)
  cv::modifies(a[0 : n])
  cv::post(cv::forall(k, 0, n, a[k] == (c & 255)))
{
  memset(a, c, n);
}
// CHECK-DAG: Verified: fill_bytes [backend=z3] [trusts=memset]

// The byte is (unsigned char)-1, 0xff.
void minus_one(int *a, int n)
  cv::pre(cv::valid(a, n) && 0 <= n && n <= 1000)
  cv::modifies(a[0 : n])
  cv::post(cv::forall(k, 0, n, a[k] == -1))
{
  memset(a, -1, n * sizeof(int));
}
// CHECK-DAG: Verified: minus_one [backend=z3] [trusts=memset]

// Each byte is 1, so each int is 0x01010101.
void wrong_fill(int *a)
  cv::pre(cv::valid(a, 2))
  cv::modifies(a[0 : 2])
  cv::post(a[0] == 1)
{
  memset(a, 1, 2 * sizeof(int));
}
// CHECK-DAG: verification failed: wrong_fill [postcondition]

bool same(const int *a, const int *b, int n)
  cv::pre(cv::valid(a, n) && cv::valid(b, n) && 0 <= n && n <= 1000)
  cv::post(cv::result == cv::forall(k, 0, n, a[k] == b[k]))
{
  return memcmp(a, b, n * sizeof(int)) == 0;
}
// CHECK-DAG: Verified: same [backend=z3] [trusts=memcmp]

int before(const unsigned char *a, const unsigned char *b, int n)
  cv::pre(cv::valid(a, n) && cv::valid(b, n) && 1 <= n && n <= 1000)
  cv::post(a[0] < b[0] ? cv::result < 0 : true)
{
  return memcmp(a, b, n);
}
// CHECK-DAG: Verified: before [backend=z3] [trusts=memcmp]

void overlap(int *a, int n)
  cv::pre(cv::valid(a, n) && 2 <= n && n <= 1000)
  cv::modifies(a[0 : n])
  cv::post(true)
{
  memcpy(a, a + 1, (n - 1) * sizeof(int));
}
// CHECK-DAG: library_models.cpp:[[@LINE-2]]:3: error: verification failed: overlap [aliasing]

void past_end(int *dst, const int *src)
  cv::pre(cv::valid(dst, 4) && cv::valid(src, 4))
  cv::modifies(dst[0 : 4])
  cv::post(true)
{
  memcpy(dst, src, 5 * sizeof(int));
}
// CHECK-DAG: verification failed: past_end

void part(int *dst, const int *src, int bytes)
  cv::pre(cv::valid(dst, 4) && cv::valid(src, 4) && 0 <= bytes && bytes <= 16)
  cv::modifies(dst[0 : 4])
  cv::post(true)
{
  memcpy(dst, src, bytes);
}
// CHECK-DAG: Unresolved: part [backend=z3] [reason=construct.unsupported] (the verifier cannot model a construct here: memcpy of a size that splits an object)

void widen(int *dst, const short *src)
  cv::pre(cv::valid(dst, 2) && cv::valid(src, 4))
  cv::modifies(dst[0 : 2])
  cv::post(true)
{
  memcpy(dst, src, 8);
}
// CHECK-DAG: error: widen: memcpy of 'int *' and 'const short *' is unsupported: it is modeled for pointers to integers of one size

void flags(bool *dst, const char *src)
  cv::pre(cv::valid(dst, 2) && cv::valid(src, 2))
  cv::modifies(dst[0 : 2])
  cv::post(true)
{
  memcpy(dst, src, 2);
}
// CHECK-DAG: error: flags: memcpy of 'bool *' and 'const char *' is unsupported: it is modeled for pointers to integers of one size

int unsequenced_size(int *dst, const int *src, int i)
  cv::pre(cv::valid(dst, 4) && cv::valid(src, 4) && 0 <= i && i < 2)
  cv::modifies(dst[0 : 4])
  cv::post(true)
{
  memcpy(dst + i, src, i++ * sizeof(int));
  return i;
}
// CHECK-DAG: error: unsequenced_size: C++ leaves the order of these call arguments open, and a call or a write in one may change what another reads

struct Pt {
  int x;
  int y;
};

void copy_point(Pt *dst, const Pt *src)
  cv::pre(dst != nullptr && src != nullptr)
  cv::modifies(*dst)
  cv::post(true)
{
  memcpy(dst, src, sizeof(Pt));
}
// CHECK-DAG: error: copy_point: memcpy of 'Pt *' and 'const Pt *' is unsupported: it is modeled for pointers to integers of one size

int magnitude(int x)
  cv::pre(x > -2147483647 - 1)
  cv::post(cv::result >= 0 && (cv::result == x || cv::result == -x))
{
  return abs(x);
}
// CHECK-DAG: Verified: magnitude [backend=z3]

long distance(long a, long b)
  cv::pre(-1000000 <= a && a <= 1000000 && -1000000 <= b && b <= 1000000)
  cv::post(cv::result == (a < b ? b - a : a - b))
{
  return std::abs(a - b);
}
// CHECK-DAG: Verified: distance [backend=z3]

int any_magnitude(int x)
  cv::post(cv::result >= 0)
{
  return abs(x);
}
// CHECK-DAG: library_models.cpp:[[@LINE-2]]:10: error: verification failed: any_magnitude [overflow]
// CHECK-DAG: note: counterexample: x = -2147483648

// In a spec, whose integers are mathematical, abs is the absolute value.
cv::spec long long magnitude_of(int x) { return abs(x); }

void spec_magnitude()
  cv::post(true)
{
  cv::check(magnitude_of(-2147483647 - 1) == 2147483648LL);
}
// CHECK-DAG: Verified: spec_magnitude [backend=z3]

// In a contract abs is C++ too: undefined at the minimum.
int abs_contract(int x)
  cv::post(cv::result == abs(x))
{
  if (x == -2147483647 - 1)
    return 0;
  return x < 0 ? -x : x;
}
// CHECK-DAG: library_models.cpp:[[@LINE-6]]:26: error: verification failed: abs_contract [overflow]
