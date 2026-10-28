// RUN: not %cpp-verify --jobs=1 %s -- > %t 2>&1
// RUN: FileCheck %s < %t
// RUN: FileCheck %s --check-prefix=SOUND < %t
//
// std::min and std::max of two integers mean what the standard says they
// mean, whatever the library: max(a, b) is a unless a < b, and min(a, b) is
// a unless b < a. The library's other functions are not modeled, and a
// constexpr helper's references to const scalars stand for their values.
//
// No proof here holds only because no execution reaches its end.
// SOUND-NOT: vacuous

#include <algorithm>

int clamp3(int x)
  cppverify::post(cppverify::result == std::max(x, 3))
{
  return x < 3 ? 3 : x;
}
// CHECK-DAG: Verified: clamp3 [backend=z3]

int lower(int a, int b)
  cppverify::post(cppverify::result == std::min(a, b))
  cppverify::post(cppverify::result <= a && cppverify::result <= b)
{
  int m = std::min(a, b);
  return m;
}
// CHECK-DAG: Verified: lower [backend=z3]

// The first argument when they are equal: std::max(a, b) is a, not b.
unsigned long widest(unsigned long a, unsigned long b)
  cppverify::post(cppverify::result >= a && cppverify::result >= b)
{
  unsigned long w = std::max(a, b);
  return w;
}
// CHECK-DAG: Verified: widest [backend=z3]

int wrong(int a, int b)
  cppverify::post(cppverify::result == std::max(a, b))
{
  return std::min(a, b);
}
// CHECK-DAG: :[[@LINE-4]]:{{[0-9]+}}: error: verification failed: wrong [postcondition]

int clamped(int x)
  cppverify::post(cppverify::result == std::clamp(x, 0, 9))
{
  return x < 0 ? 0 : (x > 9 ? 9 : x);
}
// CHECK-DAG: error: clamped: std::clamp is not modeled: of the standard library, the verifier knows std::min and std::max of two integers

template <class T>
constexpr const T &mymax(const T &a, const T &b) { return a < b ? b : a; }

int mine(int x)
  cppverify::post(cppverify::result == mymax(x, 3))
{
  return x < 3 ? 3 : x;
}
// CHECK-DAG: Verified: mine [backend=z3]

constexpr int first(const int *p) { return p[0]; }

int reads(const int *p)
  cppverify::pre(cppverify::valid(p, 1))
  cppverify::post(cppverify::result == first(p))
{
  return p[0];
}
// CHECK-DAG: error: first: a constexpr function read as a spec cannot read memory through a pointer or an array
// CHECK-DAG: Unresolved: reads [reason=construct.unsupported] (relies on first, which uses a construct the verifier does not support)

long widened(int x)
  cppverify::post(cppverify::result == std::max<long>(x, 3L))
  cppverify::post(cppverify::result >= 3)
{
  long w = std::max<long>(x, 3L);
  return w;
}
// CHECK-DAG: Verified: widened [backend=z3]

int above(int a, int b)
  cppverify::pre(a < 1000 && b < 1000)
  cppverify::post(cppverify::result > a && cppverify::result > b)
{
  return std::max(a, b) + 1;
}
// CHECK-DAG: Verified: above [backend=z3]

enum Level { Low, Mid, High };

Level highest(Level a, Level b)
  cppverify::post(cppverify::result >= a && cppverify::result >= b)
{
  Level h = std::max(a, b);
  return h;
}
// CHECK-DAG: Verified: highest [backend=z3]

cppverify::spec int spread(int a, int b) { return std::max(a, b) - std::min(a, b); }

int distance(int a, int b)
  cppverify::pre(-1000 < a && a < 1000 && -1000 < b && b < 1000)
  cppverify::post(cppverify::result == spread(a, b))
{
  return a < b ? b - a : a - b;
}
// CHECK-DAG: Verified: distance [backend=z3]

// A reference to the result is not a value: it fails closed.
int bound(int a, int b)
  cppverify::post(true)
{
  const int &r = std::max(a, b);
  return r;
}
// CHECK-DAG: error: bound: local references require a supported direct lvalue

// Of a class, std::max compares with the class's own operator<, which the
// model does not know.
struct Version {
  int v;
  constexpr bool operator<(const Version &o) const { return v < o.v; }
};

int newer(Version a, Version b)
  cppverify::post(cppverify::result == std::max(a, b).v)
{
  return a.v < b.v ? b.v : a.v;
}
// CHECK-DAG: error: newer: std::max is not modeled: of the standard library, the verifier knows std::min and std::max of two integers

// A reference the helper writes through is no value.
constexpr int bumped(int &x) {
  x = x + 1;
  return x;
}

int bumps(int x)
  cppverify::post(cppverify::result == bumped(x))
{
  return x + 1;
}
// CHECK-DAG: error: bumped: unsupported C++ type in verification: int &
// CHECK-DAG: Unresolved: bumps [reason=construct.unsupported] (relies on bumped, which uses a construct the verifier does not support)
