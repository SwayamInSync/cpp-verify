// RUN: not %cpp-verify %s 2>&1 | FileCheck %s
// RUN: not %cpp-verify --backend=bmc --unroll=2 %s 2>&1 | FileCheck %s --check-prefix=BMC
//
// A call writes only what its modifies names: a cell, the range
// p[start : length], or the object a pointer addresses (its valid(p, n)
// extent, else one object). Every other cell keeps its value, and specs
// that read only such cells keep theirs.

cppverify::spec bool valid(int *p, int n) { return true; }
cppverify::spec bool valid(const int *p, int n) { return true; }

void zero(int *q, int m)
  cppverify::pre(valid(q, m) && m >= 0 && m <= 1000)
  cppverify::modifies(*q)
  cppverify::post(cppverify::forall(k, 0, m, q[k] == 0))
{
  for (int i = 0; i < m; i = i + 1)
    cppverify::invariant(0 <= i && i <= m && cppverify::forall(k, 0, i, q[k] == 0))
    cppverify::decreases(m - i)
  {
    q[i] = 0;
  }
}
// CHECK-DAG: Verified: zero

// The slice p + lo is the callee's whole extent; the prefix and other
// objects keep their values.
void zero_tail(int *p, int n, int lo, const int *other)
  cppverify::pre(valid(p, n) && n >= 1 && n <= 1000 && 0 <= lo && lo <= n)
  cppverify::pre(valid(other, 1))
  cppverify::modifies(*p)
  cppverify::post(cppverify::forall(k, 0, lo, p[k] == cppverify::old(p[k])))
  cppverify::post(cppverify::forall(k, lo, n, p[k] == 0))
  cppverify::post(other[0] == cppverify::old(other[0]))
{
  zero(p + lo, n - lo);
}
// CHECK-DAG: Verified: zero_tail

void claims_too_much(int *p, int n, int lo)
  cppverify::pre(valid(p, n) && n >= 2 && n <= 1000 && 1 <= lo && lo < n)
  cppverify::modifies(*p)
  cppverify::post(p[lo - 1] == 0)
{
  zero(p + lo, n - lo);
}
// CHECK-DAG: error: verification failed: claims_too_much [{{.*}}::postcondition@

// A function writing a range of its buffer.
void zero_from(int *p, int n, int lo)
  cppverify::pre(valid(p, n) && n >= 1 && n <= 1000 && 0 <= lo && lo <= n)
  cppverify::modifies(p[lo : n - lo])
  cppverify::post(cppverify::forall(k, lo, n, p[k] == 0))
{
  for (int i = lo; i < n; i = i + 1)
    cppverify::invariant(lo <= i && i <= n && cppverify::forall(k, lo, i, p[k] == 0))
    cppverify::decreases(n - i)
  {
    p[i] = 0;
  }
}
// CHECK-DAG: Verified: zero_from

void keeps_prefix(int *p, int n)
  cppverify::pre(valid(p, n) && n >= 2 && n <= 1000 && p[0] == 7)
  cppverify::modifies(*p)
  cppverify::post(p[0] == 7 && p[1] == 0)
{
  zero_from(p, n, 1);
}
// CHECK-DAG: Verified: keeps_prefix

void writes_outside(int *p, int n, int lo)
  cppverify::pre(valid(p, n) && n >= 2 && n <= 1000 && 1 <= lo && lo < n)
  cppverify::modifies(p[lo : n - lo])
{
  p[lo - 1] = 0;
}
// CHECK-DAG: error: verification failed: writes_outside [{{.*}}::frame@[[@LINE-2]]:13]

void range_in_range(int *p, int n)
  cppverify::pre(valid(p, n) && n >= 4 && n <= 1000)
  cppverify::modifies(p[1 : n - 1])
{
  zero_from(p, n, 2);
}
// CHECK-DAG: Verified: range_in_range

void range_escapes(int *p, int n)
  cppverify::pre(valid(p, n) && n >= 4 && n <= 1000)
  cppverify::modifies(p[2 : n - 2])
{
  zero_from(p, n, 1);
}
// CHECK-DAG: error: verification failed: range_escapes [{{.*}}::frame@[[@LINE-2]]:3]

void writes_nothing(int *p, int n)
  cppverify::pre(valid(p, n) && n >= 1 && n <= 1000)
  cppverify::modifies(p[0 : 0])
{
}

void calls_empty(int *p, int n)
  cppverify::pre(valid(p, n) && n >= 1 && n <= 1000 && p[0] == 5)
  cppverify::post(p[0] == 5)
{
  writes_nothing(p, n);
}
// CHECK-DAG: Verified: calls_empty

// One scalar object is one cell.
void set(int *x)
  cppverify::pre(x != nullptr)
  cppverify::modifies(*x)
  cppverify::post(*x == 1)
{
  *x = 1;
}

void keeps_neighbor(int *a, int *b)
  cppverify::pre(a != nullptr && b != nullptr && *b == 5)
  cppverify::modifies(*a)
  cppverify::post(*b == 5 && *a == 1)
{
  set(a);
}
// CHECK-DAG: Verified: keeps_neighbor

// A heap-reading spec over cells a call does not write keeps its value.
cppverify::spec int total(const int *a, int n)
  cppverify::reads(a, n)
  cppverify::decreases(n)
{
  return n <= 0 ? 0 : total(a, n - 1) + a[n - 1];
}

void keeps_sum(int *out, const int *in, int n)
  cppverify::pre(valid(out, n) && valid(in, n) && n >= 0 && n <= 1000)
  cppverify::modifies(*out)
  cppverify::post(total(in, n) == cppverify::old(total(in, n)))
{
  zero(out, n);
}
// CHECK-DAG: Verified: keeps_sum

void changes_sum(int *out, int n)
  cppverify::pre(valid(out, n) && n >= 1 && n <= 1000)
  cppverify::modifies(*out)
  cppverify::post(total(out, n) == cppverify::old(total(out, n)))
{
  zero(out, n);
}
// CHECK-DAG: error: verification failed: changes_sum [{{.*}}::postcondition@

// BMC-DAG: Unresolved: keeps_prefix {{.*}}[reason=callee.contract]
// BMC-DAG: error: verification failed: writes_outside
// BMC-DAG: error: verification failed: range_escapes
// BMC-DAG: Verified: keeps_neighbor
