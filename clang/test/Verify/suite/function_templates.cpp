// RUN: not %cpp-verify --jobs=1 %s -- > %t 2>&1
// RUN: FileCheck %s < %t
// RUN: FileCheck %s --check-prefix=NOTE < %t
// RUN: FileCheck %s --check-prefix=CONVERSION < %t
// RUN: FileCheck %s --check-prefix=SOUND < %t
// RUN: grep -c "Verified: half<int>" %t | FileCheck %s --check-prefix=ONCE
// RUN: not %cpp-verify --lower-only --dump-ir=3 %s -- 2>&1 | FileCheck %s --check-prefix=VC
// RUN: not %cpp-verify --jobs=1 --diagnostics-format=json %s -- 2>/dev/null | FileCheck %s --check-prefix=JSON
//
// A function template is verified in each of its specializations, with its
// contract instantiated as its body is: what it means depends on its
// arguments. A diagnostic about a specialization notes where it is
// instantiated, as a compiler's does.
//
// No proof here holds only because no execution reaches its end.
// SOUND-NOT: vacuous

template <typename T>
T maxv(T a, T b)
  cppverify::post(cppverify::result >= a && cppverify::result >= b)
  cppverify::post(cppverify::result == a || cppverify::result == b)
{
  return a < b ? b : a;
}

int bigger(int x, int y)
  cppverify::post(cppverify::result >= x)
{
  int m = maxv(x, y);
  return m;
}
// CHECK-DAG: Verified: maxv<int> [backend=z3]
// CHECK-DAG: Verified: bigger [backend=z3]

// An explicit instantiation is verified with no caller.
template long maxv<long>(long, long);
// CHECK-DAG: Verified: maxv<long> [backend=z3]

// One instantiation may fail where another holds: 2 * 100 is no signed char.
template <typename T>
T twice(T x)
  cppverify::pre(0 <= x && x <= 100)
  cppverify::post(cppverify::result == 2 * x)
{
  return x + x;
}

int twice_int(int x)
  cppverify::pre(0 <= x && x <= 100)
{
  int r = twice(x);
  return r;
}

signed char twice_char(signed char x)
  cppverify::pre(0 <= x && x <= 100)
{
  signed char r = twice(x);
  return r;
}
// CHECK-DAG: Verified: twice<int> [backend=z3]
// CHECK-DAG: Verified: twice_int [backend=z3]
// CHECK-DAG: error: verification failed: twice<signed char> [{{.*}}::postcondition@[[@LINE-20]]:{{.*}} x [ssa=x_0] [type=i8] = {{6[4-9]|[7-9][0-9]|100}}
// CHECK-DAG: Unresolved: twice_char [backend=z3] [reason=callee.contract] (relies on the contract of twice<signed char>, which is not established)
// NOTE: error: verification failed: twice<signed char>
// NOTE-NEXT: function_templates.cpp:[[@LINE-8]]:19: note: in instantiation of function template specialization 'twice<signed char>' requested here
// JSON: "function":"twice<signed char>","instantiated_at":{"column":19,"end_column":19,"end_line":[[@LINE-9]],"file":"{{.*}}function_templates.cpp","line":[[@LINE-9]]}

// A recursive template calls its own specialization.
template <typename T>
T sum_to(T n)
  cppverify::pre(0 <= n && n <= 1000)
  cppverify::post(cppverify::result == n * (n + 1) / 2)
  cppverify::decreases(n)
{
  if (n == 0)
    return 0;
  T r = sum_to(n - 1);
  return r + n;
}

int sum_ten()
  cppverify::post(cppverify::result == 55)
{
  int s = sum_to(10);
  return s;
}
// CHECK-DAG: Verified: sum_to<int> [backend=z3]
// CHECK-DAG: Verified: sum_ten [backend=z3]

// A contract over the template's types.
template <typename T>
int bits()
  cppverify::post(cppverify::result == 8 * (int)sizeof(T))
{
  return 8 * (int)sizeof(T);
}

int widths()
  cppverify::post(cppverify::result == 80)
{
  int a = bits<short>();
  int b = bits<long long>();
  return a + b;
}
// CHECK-DAG: Verified: bits<short> [backend=z3]
// CHECK-DAG: Verified: bits<long long> [backend=z3]
// CHECK-DAG: Verified: widths [backend=z3]

// A loop contract, instantiated with the body: a short total wraps.
template <typename T>
T total(const T *p, int n)
  cppverify::pre(cppverify::valid(p, n) && 0 <= n && n <= 100)
  cppverify::pre(cppverify::forall(k, 0, n, 0 <= p[k] && p[k] <= 1000))
  cppverify::post(0 <= cppverify::result && cppverify::result <= 1000 * n)
{
  T s = 0;
  for (int i = 0; i < n; i = i + 1)
    cppverify::invariant(0 <= i && i <= n)
    cppverify::invariant(0 <= s && s <= 1000 * i)
    cppverify::decreases(n - i)
  {
    s = s + p[i];
  }
  return s;
}

int total_int(const int *p, int n)
  cppverify::pre(cppverify::valid(p, n) && 0 <= n && n <= 100)
  cppverify::pre(cppverify::forall(k, 0, n, 0 <= p[k] && p[k] <= 1000))
  cppverify::post(cppverify::result <= 100000)
{
  int t = total(p, n);
  return t;
}

short total_short(const short *p, int n)
  cppverify::pre(cppverify::valid(p, n) && 0 <= n && n <= 100)
  cppverify::pre(cppverify::forall(k, 0, n, 0 <= p[k] && p[k] <= 1000))
{
  short t = total(p, n);
  return t;
}
// CHECK-DAG: Verified: total<int> [backend=z3]
// CHECK-DAG: Verified: total_int [backend=z3]
// CHECK-DAG: error: verification failed: total<short> [{{.*}}::invariant-preserved@
// CHECK-DAG: Unresolved: total_short [backend=z3] [reason=callee.contract]
// NOTE: error: verification failed: total<short>
// NOTE-NEXT: function_templates.cpp:[[@LINE-8]]:13: note: in instantiation of function template specialization 'total<short>' requested here

// Ghost code of a template's types, a ghost variable assigned in a ghost
// block.
template <typename T>
T bump(T x)
  cppverify::pre(0 <= x && x < 100)
  cppverify::post(cppverify::result == x + 1)
{
  cppverify::ghost T before = 0;
  cppverify::ghost { before = x; }
  x = x + 1;
  cppverify::check(x == before + 1);
  return x;
}

int bump_int(int x)
  cppverify::pre(0 <= x && x < 100)
  cppverify::post(cppverify::result == x + 1)
{
  int y = bump(x);
  return y;
}
// CHECK-DAG: Verified: bump<int> [backend=z3]
// CHECK-DAG: Verified: bump_int [backend=z3]

// A spec template, applied in another template's contract.
template <typename T>
cppverify::spec bool between(T lo, T x, T hi) { return lo <= x && x <= hi; }

template <typename T>
T clamp(T x, T lo, T hi)
  cppverify::pre(lo <= hi)
  cppverify::post(between(lo, cppverify::result, hi))
{
  if (x < lo)
    return lo;
  if (hi < x)
    return hi;
  return x;
}

int clamped(int x)
  cppverify::post(0 <= cppverify::result && cppverify::result <= 10)
{
  int c = clamp(x, 0, 10);
  return c;
}
// CHECK-DAG: Verified: clamp<int> [backend=z3]
// CHECK-DAG: Verified: clamped [backend=z3]

// A contract written on a declaration, the definition after it.
template <typename T>
T half(T x)
  cppverify::pre(x >= 0)
  cppverify::post(2 * cppverify::result <= x);

template <typename T>
T half(T x)
{
  return x / 2;
}

int halved(int x)
  cppverify::pre(x >= 0)
  cppverify::post(cppverify::result <= x)
{
  int h = half(x);
  return h;
}
// CHECK-DAG: Verified: half<int> [backend=z3]
// CHECK-DAG: Verified: halved [backend=z3]
// ONCE: 1

// A member function template.
struct Meter {
  int level;

  template <typename T>
  void add(T d)
    cppverify::pre(0 <= d && d <= 100 && 0 <= level && level <= 1000)
    cppverify::modifies(level)
    cppverify::post(level == cppverify::old(level) + d)
  {
    level = level + d;
  }
};

int metered()
  cppverify::post(cppverify::result == 8)
{
  Meter m;
  m.level = 0;
  m.add(5);
  m.add((short)3);
  return m.level;
}
// CHECK-DAG: Verified: Meter::add<int> [backend=z3]
// CHECK-DAG: Verified: Meter::add<short> [backend=z3]
// CHECK-DAG: Verified: metered [backend=z3]

// A specialization the verifier cannot represent fails alone.
double fractional() { return maxv(1.5, 2.5); }
// CHECK-DAG: error: maxv<double>: unsupported C++ type in verification: double
// CONVERSION: error: maxv<double>: unsupported C++ type in verification: double
// CONVERSION: function_templates.cpp:[[@LINE-3]]:30: note: in instantiation of function template specialization 'maxv<double>' requested here

// Never instantiated: not verified.
template <typename T>
T unused(T x)
  cppverify::post(cppverify::result == x)
{
  return x;
}
// CHECK-DAG: function_templates.cpp:[[@LINE-5]]:3: warning: unused: function template is not verified: this translation unit instantiates none of its specializations

// A trusted template declared without a definition: its contract is
// instantiated where it is used.
template <typename T>
[[cppverify::trusted]] T next_of(T x)
  cppverify::pre(x < 100)
  cppverify::post(cppverify::result == x + 1);

int uses_next()
  cppverify::post(cppverify::result == 6)
{
  int r = next_of(5);
  return r;
}
// CHECK-DAG: Trusted: next_of<int> (contract assumed, not verified)
// CHECK-DAG: Verified: uses_next [backend=z3] [trusts=next_of<int>]

// cppverify::result of the template's type, compared with a constant.
template <typename T>
T magnitude(T x)
  cppverify::pre(x > -1000 && x < 1000)
  cppverify::post(cppverify::result >= 0)
{
  return x < 0 ? -x : x;
}

int uses_magnitude(int x)
  cppverify::pre(x > -1000 && x < 1000)
  cppverify::post(cppverify::result >= 0)
{
  int m = magnitude(x);
  return m;
}
// CHECK-DAG: Verified: magnitude<int> [backend=z3]
// CHECK-DAG: Verified: uses_magnitude [backend=z3]

// A loop whose condition and body do not change with the template's
// arguments still gets its instantiated contract.
template <typename T>
int size_of()
  cppverify::post(cppverify::result == (int)sizeof(T))
{
  while (false)
    cppverify::invariant(sizeof(T) >= 1)
  {
  }
  return (int)sizeof(T);
}

int sizes()
  cppverify::post(cppverify::result == 6)
{
  int s = size_of<short>();
  int i = size_of<int>();
  return s + i;
}
// CHECK-DAG: Verified: size_of<short> [backend=z3]
// CHECK-DAG: Verified: size_of<int> [backend=z3]
// CHECK-DAG: Verified: sizes [backend=z3]

// A trigger stays one in each specialization.
template <typename T>
T first_positive(const T *a, int n)
  cppverify::pre(cppverify::valid(a, n) && 0 < n)
  cppverify::pre(cppverify::forall(k, 0, n, cppverify::trigger(a[k]) > 0))
  cppverify::post(cppverify::result > 0)
{
  T v = a[0];
  return v;
}

int first_int(const int *a, int n)
  cppverify::pre(cppverify::valid(a, n) && 0 < n)
  cppverify::pre(cppverify::forall(k, 0, n, a[k] > 0))
  cppverify::post(cppverify::result > 0)
{
  int v = first_positive(a, n);
  return v;
}
// CHECK-DAG: Verified: first_positive<int> [backend=z3]
// CHECK-DAG: Verified: first_int [backend=z3]
// VC-LABEL: vc first_positive<int>
// VC: forall
// VC: trigger
// VC-NEXT: heap_select
// VC-LABEL: vc first_int

// An uncontracted constexpr template in a contract is a spec in each
// specialization, as a constexpr function is.
template <typename T>
constexpr T bigger_of(T a, T b) { return a < b ? b : a; }

int clamp3(int x)
  cppverify::post(cppverify::result == bigger_of(x, 3))
{
  return x < 3 ? 3 : x;
}
// CHECK-DAG: Verified: clamp3 [backend=z3]

// A contract written on the definition, after a declaration that names its
// parameter otherwise and before which the template is used.
template <typename T>
T third(T x);

int thirds(int x)
  cppverify::pre(x >= 0)
  cppverify::post(cppverify::result <= x)
{
  int t = third(x);
  return t;
}

template <typename T>
T third(T y)
  cppverify::pre(y >= 0)
  cppverify::post(3 * cppverify::result <= y)
{
  return y / 3;
}
// CHECK-DAG: Verified: third<int> [backend=z3]
// CHECK-DAG: Verified: thirds [backend=z3]

// A variadic template: a fold over a quantifier binds a variable in each
// element, and the parameters the pack expands to are named apart.
template <typename... Ns>
int first_small(const int *p, Ns... ns)
  cppverify::pre(cppverify::valid(p, 10))
  cppverify::pre(((0 < ns && ns <= 10) && ...))
  cppverify::pre((cppverify::forall(k, 0, ns, p[k] < 10) && ...))
  cppverify::post(cppverify::result < 10)
{
  return p[0];
}

int uses_first_small(const int *p)
  cppverify::pre(cppverify::valid(p, 10))
  cppverify::pre(cppverify::forall(k, 0, 10, p[k] < 10))
  cppverify::post(cppverify::result < 10)
{
  int v = first_small(p, 3, 5);
  return v;
}
// CHECK-DAG: Verified: first_small<int, int> [backend=z3]
// CHECK-DAG: Verified: uses_first_small [backend=z3]

template <typename... Ns>
int product_of(Ns... ns)
  cppverify::pre(((0 <= ns && ns <= 10) && ...))
  cppverify::post(cppverify::result == (ns * ...))
{
  return (ns + ...);
}

int products() { return product_of(2, 3); }
// CHECK-DAG: error: verification failed: product_of<int, int> [{{.*}}::postcondition@[[@LINE-6]]:{{.*}} ns...[0] [ssa=ns...[0]_0] [type=i32] = {{.*}} ns...[1] [ssa=ns...[1]_0] [type=i32] =
