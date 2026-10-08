// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s --check-prefixes=CHECK,DEDUCTIVE
// RUN: not %cpp-verify --backend=bmc --unroll=1 %s -- 2>&1 | FileCheck %s --check-prefixes=CHECK,BMC
// RUN: not %cpp-verify --int-encoding=integer %s -- 2>&1 | FileCheck %s --check-prefixes=CHECK,DEDUCTIVE
//
// Contract arithmetic is mathematical, as in ACSL and Verus spec code:
// integer operands are read exactly, no operation wraps or overflows, and an
// implicit conversion keeps the value. Division by zero is still undefined.
// Bitwise operators, shifts, and explicit casts are machine operations, and a
// cast of a value that does not fit is an overflow.

unsigned add_wraps(unsigned a, unsigned b)
  cppverify::post(cppverify::result == a + b)
{
  return a + b;
}
// CHECK-DAG: error: verification failed: add_wraps [{{.*}}::postcondition@{{.*}}b [ssa=b_0] [type=u32] =

unsigned add_mod(unsigned a, unsigned b)
  cppverify::post(cppverify::result == (a + b) % 4294967296)
{
  return a + b;
}
// CHECK-DAG: Verified: add_mod

int inc(int x)
  cppverify::pre(x < 2147483647)
  cppverify::post(cppverify::result == x + 1 && cppverify::result > x)
{
  return x + 1;
}
// CHECK-DAG: Verified: inc

long widen(int x)
  cppverify::post(cppverify::result == x * 2)
{
  return (long)x * 2;
}
// CHECK-DAG: Verified: widen

bool below(int x, unsigned n)
  cppverify::pre(n >= 1)
  cppverify::post(cppverify::result == (x < n))
{
  return x < 0 || (unsigned)x < n;
}
// CHECK-DAG: Verified: below

bool is_max(unsigned u)
  cppverify::post(cppverify::result == (u == -1))
{
  return u == 4294967295u;
}
// CHECK-DAG: warning: contract arithmetic is mathematical: the negative value -1 keeps its value here instead of converting to unsigned int
// CHECK-DAG: error: verification failed: is_max [{{.*}}::postcondition@

int quotient(int x, int y)
  cppverify::pre(y != 0 && !(x == -2147483647 - 1 && y == -1))
  cppverify::post(cppverify::result == x / y)
{
  return x / y;
}
// CHECK-DAG: Verified: quotient

void divides_by_zero(int x, int y)
  cppverify::post(x / y == x / y)
{
}
// CHECK-DAG: error: verification failed: divides_by_zero [{{.*}}::division-by-zero@

int even(int x)
  cppverify::pre(x >= 0 && x < 1000)
  cppverify::post((cppverify::result & 1) == 0 && cppverify::result == 2 * x)
{
  return 2 * x;
}
// CHECK-DAG: Verified: even

int narrowed(int x)
  cppverify::pre(x == 256)
  cppverify::post((unsigned char)x == 0)
{
  return 0;
}
// CHECK-DAG: Verified: narrowed

int cast_overflows(int x)
  cppverify::pre(x == 2147483647)
  cppverify::post((int)(x + 1) < 0)
{
  return 0;
}
// CHECK-DAG: error: verification failed: cast_overflows [{{.*}}::overflow@

constexpr int twice(int v) { return v + v; }

void binder_to_machine(int n)
  cppverify::pre(n >= 0 && n < 100)
{
  cppverify::check(cppverify::forall(k, 0, n, twice(k) == 2 * k));
}
// CHECK-DAG: Verified: binder_to_machine

cppverify::spec bool valid(int *p, int n) { return true; }

void reverse(int *a, int n)
  cppverify::pre(valid(a, n) && n >= 0 && n <= 100000)
  cppverify::modifies(*a)
  cppverify::post(cppverify::forall(k, 0, n, a[k] == cppverify::old(a[n - 1 - k])))
{
  int i = 0;
  int j = n - 1;
  while (i < j)
    cppverify::invariant(0 <= i && i <= n && j == n - 1 - i && i <= j + 1)
    cppverify::invariant(cppverify::forall(k, 0, i, a[k] == cppverify::old(a[n - 1 - k])))
    cppverify::invariant(cppverify::forall(k, j + 1, n, a[k] == cppverify::old(a[n - 1 - k])))
    cppverify::invariant(cppverify::forall(k, i, j + 1, a[k] == cppverify::old(a[k])))
    cppverify::decreases(j - i)
  {
    int t = a[i];
    a[i] = a[j];
    a[j] = t;
    i = i + 1;
    j = j - 1;
  }
}
// DEDUCTIVE-DAG: Verified: reverse
// BMC-DAG: BoundedSafe: reverse
