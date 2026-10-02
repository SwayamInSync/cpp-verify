// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefixes=CHECK,DEDUCTIVE
// RUN: not %cpp-verify --backend=bmc --unroll=1 %s 2>&1 | FileCheck %s --check-prefixes=CHECK,BMC
// RUN: not %cpp-verify --int-encoding=integer %s 2>&1 | FileCheck %s --check-prefixes=CHECK,DEDUCTIVE
//
// Contract arithmetic is mathematical, as in ACSL and Verus spec code:
// integer operands are read exactly, no operation wraps or overflows, and an
// implicit conversion keeps the value. Division by zero is still undefined.
// Bitwise operators, shifts, and explicit casts are machine operations, and a
// cast of a value that does not fit is an overflow.

unsigned add_wraps(unsigned a, unsigned b)
  post(result == a + b)
{
  return a + b;
}
// CHECK-DAG: error: verification failed: add_wraps [{{.*}}::postcondition@{{.*}}b [ssa=b_0] [type=u32] =

unsigned add_mod(unsigned a, unsigned b)
  post(result == (a + b) % 4294967296)
{
  return a + b;
}
// CHECK-DAG: Verified: add_mod

int inc(int x)
  pre(x < 2147483647)
  post(result == x + 1 && result > x)
{
  return x + 1;
}
// CHECK-DAG: Verified: inc

long widen(int x)
  post(result == x * 2)
{
  return (long)x * 2;
}
// CHECK-DAG: Verified: widen

bool below(int x, unsigned n)
  pre(n >= 1)
  post(result == (x < n))
{
  return x < 0 || (unsigned)x < n;
}
// CHECK-DAG: Verified: below

bool is_max(unsigned u)
  post(result == (u == -1))
{
  return u == 4294967295u;
}
// CHECK-DAG: warning: contract arithmetic is mathematical: the negative value -1 keeps its value here instead of converting to unsigned int
// CHECK-DAG: error: verification failed: is_max [{{.*}}::postcondition@

int quotient(int x, int y)
  pre(y != 0 && !(x == -2147483647 - 1 && y == -1))
  post(result == x / y)
{
  return x / y;
}
// CHECK-DAG: Verified: quotient

void divides_by_zero(int x, int y)
  post(x / y == x / y)
{
}
// CHECK-DAG: error: verification failed: divides_by_zero [{{.*}}::division-by-zero@

int even(int x)
  pre(x >= 0 && x < 1000)
  post((result & 1) == 0 && result == 2 * x)
{
  return 2 * x;
}
// CHECK-DAG: Verified: even

int narrowed(int x)
  pre(x == 256)
  post((unsigned char)x == 0)
{
  return 0;
}
// CHECK-DAG: Verified: narrowed

int cast_overflows(int x)
  pre(x == 2147483647)
  post((int)(x + 1) < 0)
{
  return 0;
}
// CHECK-DAG: error: verification failed: cast_overflows [{{.*}}::overflow@

constexpr int twice(int v) { return v + v; }

void binder_to_machine(int n)
  pre(n >= 0 && n < 100)
{
  contract_assert(forall(k, 0, n, twice(k) == 2 * k));
}
// CHECK-DAG: Verified: binder_to_machine

spec bool valid(int *p, int n) { return true; }

void reverse(int *a, int n)
  pre(valid(a, n) && n >= 0 && n <= 100000)
  modifies(*a)
  post(forall(k, 0, n, a[k] == old(a[n - 1 - k])))
{
  int i = 0;
  int j = n - 1;
  while (i < j)
    invariant(0 <= i && i <= n && j == n - 1 - i && i <= j + 1)
    invariant(forall(k, 0, i, a[k] == old(a[n - 1 - k])))
    invariant(forall(k, j + 1, n, a[k] == old(a[n - 1 - k])))
    invariant(forall(k, i, j + 1, a[k] == old(a[k])))
    decreases(j - i)
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
