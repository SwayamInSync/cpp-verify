// RUN: not %cpp-verify --jobs=1 %s -- -std=c++20 > %t 2>&1
// RUN: FileCheck %s < %t
// RUN: FileCheck %s --check-prefix=SOUND < %t
//
// Small forms of everyday C++: character literals, constants Clang
// evaluates, template value parameters, default arguments, declarations
// without effect, __builtin_expect, a record returned from an initializer
// list, and structured bindings. Every correct function has a wrong twin
// that must be refuted.
//
// No proof here holds only because no execution reaches its end.
// SOUND-NOT: vacuous

namespace cv = cppverify;

// A character literal is an integer of its type.
bool is_digit(char c)
  cv::post(cv::result == ('0' <= c && c <= '9'))
{
  return c >= '0' && c <= '9';
}
// CHECK-DAG: Verified: is_digit [backend=z3]

bool is_digit_wrong(char c)
  cv::post(cv::result == ('0' <= c && c < '9'))
{
  return c >= '0' && c <= '9';
}
// CHECK-DAG: error: verification failed: is_digit_wrong {{.*}}[reason=counterexample]
// CHECK-DAG: note: counterexample: {{.*}}c = 57{{( ->|,|$)}}

int digit_value(char c)
  cv::pre('0' <= c && c <= '9')
  cv::post(0 <= cv::result && cv::result <= 9)
{
  return c - '0';
}
// CHECK-DAG: Verified: digit_value [backend=z3]

// A character literal has its type's value: '\xff' is -1 as a signed char.
bool high_char(signed char c)
  cv::post(cv::result == (c == -1))
{
  return c == '\xff';
}
// CHECK-DAG: Verified: high_char [backend=z3]

int wide(wchar_t c)
  cv::post(cv::result == (c == 65))
{
  return c == L'A';
}
// CHECK-DAG: Verified: wide [backend=z3]

// A consteval call and an if constexpr condition are the values Clang
// computes; a template value parameter is its argument.
consteval int limit() { return 100; }

int clamp(int x)
  cv::post(cv::result <= 100)
{
  if (x > limit())
    return limit();
  return x;
}
// CHECK-DAG: Verified: clamp [backend=z3]

int clamp_wrong(int x)
  cv::post(cv::result < 100)
{
  if (x > limit())
    return limit();
  return x;
}
// CHECK-DAG: error: verification failed: clamp_wrong [{{.*}}[reason=counterexample]

template <int N> int scaled(int x)
  cv::pre(-1000 <= x && x <= 1000)
  cv::post(cv::result == N * x)
{
  if constexpr (N == 0)
    return 0;
  else
    return N * x;
}

int scaled_twice(int x)
  cv::pre(-1000 <= x && x <= 1000)
  cv::post(cv::result == 3 * x)
{
  return scaled<0>(x) + scaled<3>(x);
}
// CHECK-DAG: Verified: scaled<0> [backend=z3]
// CHECK-DAG: Verified: scaled<3> [backend=z3]
// CHECK-DAG: Verified: scaled_twice [backend=z3]

int scaled_wrong(int x)
  cv::pre(-1000 <= x && x <= 1000)
  cv::post(cv::result == 4 * x)
{
  return scaled<0>(x) + scaled<3>(x);
}
// CHECK-DAG: error: verification failed: scaled_wrong [{{.*}}[reason=counterexample]

// A default argument is evaluated at the call.
int add(int x, int y = 2)
  cv::pre(-1000 <= x && x <= 1000 && -1000 <= y && y <= 1000)
  cv::post(cv::result == x + y)
{
  return x + y;
}
// CHECK-DAG: Verified: add [backend=z3]

int add_default(int x)
  cv::pre(-1000 <= x && x <= 1000)
  cv::post(cv::result == x + 2)
{
  return add(x);
}
// CHECK-DAG: Verified: add_default [backend=z3]

int add_default_wrong(int x)
  cv::pre(-1000 <= x && x <= 1000)
  cv::post(cv::result == x)
{
  return add(x);
}
// CHECK-DAG: error: verification failed: add_default_wrong [{{.*}}[reason=counterexample]

// static_assert, type aliases, using-declarations, and local types declare,
// and do nothing.
int declarations(int x)
  cv::pre(-1000 <= x && x <= 1000)
  cv::post(cv::result == x + 1)
{
  static_assert(sizeof(int) == 4);
  typedef int counter;
  using other = int;
  enum Step { One = 1 };
  struct Box { int v; };
  counter c = x;
  other d = c + One;
  return d;
}
// CHECK-DAG: Verified: declarations [backend=z3]

// __builtin_expect(e, c) is e.
int expect(int x)
  cv::post(cv::result == (x > 0 ? 1 : 0))
{
  if (__builtin_expect(x > 0, 1))
    return 1;
  return 0;
}
// CHECK-DAG: Verified: expect [backend=z3]

int expect_wrong(int x)
  cv::post(cv::result == 1)
{
  if (__builtin_expect(x > 0, 1))
    return 1;
  return 0;
}
// CHECK-DAG: error: verification failed: expect_wrong [{{.*}}[reason=counterexample]

// A record returned from an initializer list.
struct Pt {
  int x;
  int y;
};

Pt make(int a, int b)
  cv::post(cv::result.x == a && cv::result.y == b)
{
  return Pt{a, b};
}
// CHECK-DAG: Verified: make [backend=z3]

Pt make_braced(int a)
  cv::post(cv::result.x == a && cv::result.y == 0)
{
  return {a};
}
// CHECK-DAG: Verified: make_braced [backend=z3]

Pt make_wrong(int a, int b)
  cv::post(cv::result.x == b)
{
  return Pt{a, b};
}
// CHECK-DAG: error: verification failed: make_wrong [{{.*}}[reason=counterexample]

// Structured bindings name the fields of a copy.
int sum(Pt p)
  cv::pre(-1000 <= p.x && p.x <= 1000 && -1000 <= p.y && p.y <= 1000)
  cv::post(cv::result == p.x + p.y)
{
  auto [a, b] = p;
  return a + b;
}
// CHECK-DAG: Verified: sum [backend=z3]

int first(Pt p)
  cv::post(cv::result == p.y)
{
  auto [a, b] = p;
  return a;
}
// CHECK-DAG: error: verification failed: first [{{.*}}[reason=counterexample]

int both(Pt p, Pt q)
  cv::post(cv::result == p.x)
{
  auto [a, b] = p;
  auto [c, d] = q;
  return a;
}
// CHECK-DAG: Verified: both [backend=z3]
