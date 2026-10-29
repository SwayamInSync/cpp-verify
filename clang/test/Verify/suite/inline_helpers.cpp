// RUN: not %cpp-verify --jobs=1 %s -- > %t 2>&1
// RUN: FileCheck %s < %t
// RUN: FileCheck %s --check-prefix=QUIET < %t
// RUN: %cpp-verify --lower-only --dump-ir=1 --function=index_of %s -- | FileCheck %s --check-prefix=L1
// RUN: %cpp-verify --lower-only --dump-ir=1 --function=use_mid %s -- | FileCheck %s --check-prefix=CLOSED
// RUN: %cpp-verify --lower-only --dump-ir=3 --function=use_six %s -- | FileCheck %s --check-prefix=FUEL
//
// A call of a function with a body and no contract runs that body: the
// verifier inlines it at the call, so the caller's proof covers it at the
// arguments the caller passes, and the helper's checks are the caller's. A
// helper is verified where verified code calls it, not on its own.
//
// QUIET-NOT: {{(Verified|failed|Unresolved): (add_one|count_zeros|halve|sign|bump|abs_diff|grade|six) }}
// QUIET-NOT: error: {{(down|with_goto|h10):}}

namespace cv = cppverify;

int add_one(int x) { return x + 1; }
// CHECK-DAG: inline_helpers.cpp:[[@LINE-1]]:31: error: verification failed: next [overflow]

int twice_plus_one(int x)
  cv::pre(0 <= x && x < 1000)
  cv::post(cv::result == 2 * x + 1)
{
  return add_one(x) + x;
}
// CHECK-DAG: Verified: twice_plus_one [backend=z3]

// The same helper where its addition overflows: the failure is at the
// helper's operation, in the caller's verdict, with the helper's values.
int next(int x)
  cv::post(cv::result == x + 1)
{
  return add_one(x);
}
// CHECK-DAG: note: counterexample: add_one::x = 2147483647, x = 2147483647

// Early returns.
int sign(int x)
{
  if (x < 0)
    return -1;
  if (x > 0)
    return 1;
  return 0;
}

int magnitude(int x)
  cv::pre(-1000 <= x && x <= 1000)
  cv::post(cv::result >= 0)
{
  return sign(x) * x;
}
// CHECK-DAG: Verified: magnitude [backend=z3]

int positive_sign(int x)
  cv::post(cv::result > 0)
{
  return sign(x);
}
// CHECK-DAG: error: verification failed: positive_sign [postcondition]

int exact_sign(int x)
  cv::post(cv::result == (x < 0 ? -1 : (x > 0 ? 1 : 0)))
{
  return sign(x);
}
// CHECK-DAG: Verified: exact_sign [backend=z3]

// A helper's variables are apart from the caller's of the same name.
int bump(int v)
{
  int c = v + 1;
  return c;
}

int keeps_own_variables(int c)
  cv::pre(0 <= c && c < 1000)
  cv::post(cv::result == 2 * c + 1)
{
  int r = bump(c);
  return r + c;
}
// CHECK-DAG: Verified: keeps_own_variables [backend=z3]

// Writes through a pointer, checked against the caller's frame and extent.
void put(int *p, int v) { *p = v; }

void set_first(int *a, int n)
  cv::pre(cv::valid(a, n) && n >= 1)
  cv::modifies(a[0])
  cv::post(a[0] == 7)
{
  put(a, 7);
}
// CHECK-DAG: Verified: set_first [backend=z3]

void set_second(int *a, int n)
  cv::pre(cv::valid(a, n) && n >= 2)
  cv::modifies(a[0])
{
  put(a + 1, 7);
}
// CHECK-DAG: error: verification failed: set_second [frame]

void set_past(int *a, int n)
  cv::pre(cv::valid(a, n) && n >= 1)
  cv::modifies(a[0 : n])
{
  put(a + n, 7);
}
// CHECK-DAG: error: verification failed: set_past [bounds]

// A loop with its invariant, verified at each call with the caller's extent;
// on its own, without a precondition, its reads would not be.
int count_zeros(const int *a, int n)
{
  int c = 0;
  for (int i = 0; i < n; i = i + 1)
    cv::invariant(0 <= i && i <= n && 0 <= c && c <= i)
    cv::decreases(n - i)
  {
    if (a[i] == 0)
      // CHECK-DAG: inline_helpers.cpp:[[@LINE-1]]:9: error: verification failed: zeros_past [bounds]
      c = c + 1;
  }
  return c;
}

int zeros(const int *a, int n)
  cv::pre(cv::valid(a, n) && 0 <= n && n <= 1000)
  cv::post(0 <= cv::result && cv::result <= n)
{
  return count_zeros(a, n);
}
// CHECK-DAG: Verified: zeros [backend=z3]

int zeros_past(const int *a, int n)
  cv::pre(cv::valid(a, n) && 0 <= n && n <= 1000)
{
  return count_zeros(a, n + 1);
}
// CHECK-DAG: count_zeros::i = 0 -> 1

// A return inside a loop leaves the helper.
int find(const int *a, int n, int v)
{
  for (int i = 0; i < n; i = i + 1)
    cv::invariant(0 <= i && i <= n)
    cv::decreases(n - i)
  {
    if (a[i] == v)
      return i;
  }
  return -1;
}

int index_of(const int *a, int n, int v)
  cv::pre(cv::valid(a, n) && 0 <= n && n <= 1000)
  cv::post(cv::result == -1 || (0 <= cv::result && cv::result < n &&
                                a[cv::result] == v))
{
  return find(a, n, v);
}
// CHECK-DAG: Verified: index_of [backend=z3]

// L1:      assign __inline1_find$a
// L1:      assign __inline1_find$__returned
// L1-NEXT:   false
// L1-NEXT: assign __inline1_find$__result
// L1-NEXT:   0
// L1:      while
// L1:          !
// L1-NEXT:       __inline1_find$__returned
// L1:          assign __inline1_find$__result
// L1-NEXT:       __inline1_find$i
// L1-NEXT:     assign __inline1_find$__returned
// L1-NEXT:       true
// L1-NEXT:     break
// L1:      if
// L1-NEXT:   !
// L1-NEXT:     __inline1_find$__returned
// L1-NEXT:   assign __inline1_find$__result
// L1:      assign __return_call_{{[0-9]+}}
// L1-NEXT:   __inline1_find$__result

// A return inside an inner loop leaves both loops.
int first_sum(int n, int s)
{
  for (int i = 0; i < n; i = i + 1)
    cv::invariant(0 <= i && i <= n)
    cv::decreases(n - i)
  {
    for (int j = 0; j < n; j = j + 1)
      cv::invariant(0 <= j && j <= n)
      cv::decreases(n - j)
    {
      if (i + j == s)
        return i;
    }
  }
  return -1;
}

int sum_row(int n, int s)
  cv::pre(0 <= n && n <= 100 && 0 <= s && s <= 300)
  cv::post(cv::result == -1 || (0 <= cv::result && cv::result < n))
{
  return first_sum(n, s);
}
// CHECK-DAG: Verified: sum_row [backend=z3]

int index_of_wrong(const int *a, int n, int v)
  cv::pre(cv::valid(a, n) && 0 <= n && n <= 1000)
  cv::post(cv::result >= 0)
{
  return find(a, n, v);
}
// CHECK-DAG: error: verification failed: index_of_wrong [postcondition]

// Helpers call helpers, and contracted functions, whose preconditions are
// checked at each call.
int clamp_to(int x, int hi)
  cv::pre(0 <= hi)
  cv::post(0 <= cv::result && cv::result <= hi)
{
  return x < 0 ? 0 : x > hi ? hi : x;
}

int scaled(int x) { return clamp_to(add_one(x), 100) * 2; }

int percent(int x)
  cv::pre(0 <= x && x < 1000)
  cv::post(0 <= cv::result && cv::result <= 200)
{
  return scaled(x);
}
// CHECK-DAG: Verified: percent [backend=z3]

int clamp_negative(int x) { return clamp_to(x, -1); }

int use_negative(int x)
  cv::post(cv::result <= 0)
{
  return clamp_negative(x);
}
// CHECK-DAG: error: verification failed: use_negative [precondition]

// Member functions, and a helper's assertion.
class Box {
public:
  int v;
  int value() const { return v; }
  void store(int x) { v = x; }
};

int read_box(const Box &b)
  cv::post(cv::result == b.v)
{
  return b.value();
}
// CHECK-DAG: Verified: read_box [backend=z3]

void put_box(Box &b, int x)
  cv::modifies(b)
  cv::post(b.v == x)
{
  b.store(x);
}
// CHECK-DAG: Verified: put_box [backend=z3]

int halve(int x)
{
  cv::check(x % 2 == 0);
  return x / 2;
}

int quarter(int x)
  cv::pre(x % 4 == 0)
  cv::post(4 * cv::result == x)
{
  return halve(halve(x));
}
// CHECK-DAG: Verified: quarter [backend=z3]

int half_odd(int x)
  cv::pre(x % 4 == 2)
{
  return halve(halve(x));
}
// CHECK-DAG: error: verification failed: half_odd [assertion]

// A record by value is its fields.
struct Pt { int x; int y; };
int sum(Pt p) { return p.x + p.y; }

int use_sum(int a)
  cv::pre(0 <= a && a < 100)
  cv::post(cv::result == 2 * a)
{
  Pt p{a, a};
  return sum(p);
}
// CHECK-DAG: Verified: use_sum [backend=z3]

// A helper that writes nothing its caller sees may stand beside another
// call or a read, in either operand; one that writes what the other operand
// reads is ordered as a call with a frame is.
int abs_diff(int a, int b) { return a < b ? b - a : a - b; }

int spread(int a, int b, int c, int d)
  cv::pre(0 <= a && a < 1000 && 0 <= b && b < 1000)
  cv::pre(0 <= c && c < 1000 && 0 <= d && d < 1000)
  cv::post(cv::result >= 0)
{
  return abs_diff(a, b) + abs_diff(c, d);
}
// CHECK-DAG: Verified: spread [backend=z3]

int push(int *p) { *p = *p + 1; return *p; }

int push_and_read(int *p)
  cv::pre(cv::valid(p, 1) && *p < 1000)
  cv::modifies(*p)
{
  return push(p) + *p;
}
// CHECK-DAG: error: push_and_read: C++ leaves the order of these operands open

// Returns in a switch.
int grade(int score)
{
  switch (score / 10) {
  case 10:
  case 9:
    return 4;
  case 8:
    return 3;
  default:
    break;
  }
  return 0;
}

int use_grade(int s)
  cv::pre(0 <= s && s <= 100)
  cv::post(0 <= cv::result && cv::result <= 4)
  cv::post(s < 90 || cv::result == 4)
{
  return grade(s);
}
// CHECK-DAG: Verified: use_grade [backend=z3]

int grade_wrong(int s)
  cv::pre(0 <= s && s <= 100)
  cv::post(cv::result >= 3)
{
  return grade(s);
}
// CHECK-DAG: error: verification failed: grade_wrong [postcondition]

// A helper's reveal_with_fuel unfolds its specs where it is inlined.
cv::spec int tri(int n)
  cv::decreases(n)
{
  return n <= 0 ? 0 : tri(n - 1) + n;
}

int six()
{
  cv::reveal_with_fuel(tri, 4);
  return 6;
}

int use_six()
  cv::post(cv::result == tri(3))
{
  return six();
}
// CHECK-DAG: Verified: use_six [backend=z3]
// FUEL: fuel 4

// What inlining does not support fails closed, asking for a contract.
int down(int n) { return n <= 0 ? 0 : down(n - 1); }

int use_down(int n)
  cv::pre(0 <= n && n <= 10)
  cv::post(cv::result == 0)
{
  return down(n);
}
// CHECK-DAG: Unresolved: use_down [backend=z3] [reason=construct.unsupported] ({{.*}}down has no contract and calls itself, so its body cannot be inlined; give it a contract)

int even(int n);
int odd(int n) { return n == 0 ? 0 : even(n - 1); }
int even(int n) { return n == 0 ? 1 : odd(n - 1); }

int use_even(int n)
  cv::pre(0 <= n && n < 4)
{
  return even(n);
}
// CHECK-DAG: Unresolved: use_even {{.*}}the functions without contracts even -> odd -> even call each other, so their bodies cannot be inlined; give one of them a contract)

int grow(int *p, int n)
{
  for (int i = 0; i < n; i = i + 1)
    cv::invariant(0 <= i && i <= n && *p == cv::old(*p) + i)
    cv::decreases(n - i)
  {
    *p = *p + 1;
  }
  return *p;
}

int use_grow(int *p)
  cv::pre(p != nullptr && *p == 0)
  cv::modifies(*p)
  cv::post(cv::result == 3)
{
  return grow(p, 3);
}
// CHECK-DAG: Unresolved: use_grow {{.*}}grow has no contract and its loop invariants use cppverify::old, whose entry would be the caller's if it were inlined; give it a contract)

Pt mid(Pt a, Pt b) { return Pt{(a.x + b.x) / 2, (a.y + b.y) / 2}; }

int use_mid(int a)
  cv::pre(0 <= a && a < 100)
{
  Pt p{a, a};
  Pt q = mid(p, p);
  return q.x;
}
// CHECK-DAG: Unresolved: use_mid {{.*}}mid has no contract and returns a record by value, which inlining does not support; give it a contract)
// The path ends at the call, so that no later check can fail on a value
// the call would have produced.
// CLOSED:      assert unsupported
// CLOSED-NEXT:   false
// CLOSED-NEXT: assume
// CLOSED-NEXT:   false
// CLOSED-NEXT: return

int with_goto(int x)
{
  if (x > 0)
    goto end;
  // CHECK-DAG: Unresolved: use_goto {{.*}}with_goto has no contract, and its body cannot be inlined (with_goto: goto is unsupported at [[@LINE-1]]:5); give it a contract)
  x = 1;
end:
  return x;
}

int use_goto(int x)
  cv::pre(0 <= x && x < 10)
{
  return with_goto(x);
}

// Inlining that would grow without bound stops at a budget.
int h0(int x) { return x + 1; }
int h1(int x) { int a = h0(x); int b = h0(x); return a - b; }
int h2(int x) { int a = h1(x); int b = h1(x); return a - b; }
int h3(int x) { int a = h2(x); int b = h2(x); return a - b; }
int h4(int x) { int a = h3(x); int b = h3(x); return a - b; }
int h5(int x) { int a = h4(x); int b = h4(x); return a - b; }
int h6(int x) { int a = h5(x); int b = h5(x); return a - b; }
int h7(int x) { int a = h6(x); int b = h6(x); return a - b; }
int h8(int x) { int a = h7(x); int b = h7(x); return a - b; }
int h9(int x) { int a = h8(x); int b = h8(x); return a - b; }
int h10(int x) { int a = h9(x); int b = h9(x); return a - b; }

int use_h3(int x)
  cv::pre(0 <= x && x < 10)
  cv::post(cv::result == 0)
{
  return h3(x);
}
// CHECK-DAG: Verified: use_h3 [backend=z3]

int use_h10(int x)
  cv::pre(0 <= x && x < 10)
{
  return h10(x);
}
// CHECK-DAG: Unresolved: use_h10 {{.*}}the bodies of the functions without contracts that use_h10 runs would be more than 2000 statements inlined; give h10 a contract)
