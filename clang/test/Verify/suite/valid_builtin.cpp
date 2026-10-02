// RUN: not %cpp-verify %s 2>&1 | FileCheck %s
//
// <cppverify.h> provides valid(p, n) for every pointee type: in a
// precondition it declares that p points to n objects, p[0] to p[n - 1]. A
// user-declared spec bool valid(T *p, int n) { return true; } means the same.

#include <cppverify.h>
using cppverify::valid;

struct point { int x; int y; };

int sum2(const int *a, int n)
  pre(valid(a, n) && n >= 2)
  pre(a[0] >= 0 && a[0] <= 1000 && a[1] >= 0 && a[1] <= 1000)
  post(result == a[0] + a[1])
{
  return a[0] + a[1];
}
// CHECK-DAG: Verified: sum2

void fill(int *a, int n)
  pre(cppverify::valid(a, n) && n >= 0 && n <= 1000)
  modifies(*a)
  post(forall(k, 0, n, a[k] == 7))
{
  for (int i = 0; i < n; i = i + 1)
    invariant(0 <= i && i <= n && forall(k, 0, i, a[k] == 7))
    decreases(n - i)
  {
    a[i] = 7;
  }
}
// CHECK-DAG: Verified: fill

// The callee's extent is the slice a + lo; the prefix keeps its values.
void fill_tail(int *a, int n, int lo)
  pre(valid(a, n) && n >= 1 && n <= 1000 && 0 <= lo && lo <= n)
  modifies(*a)
  post(forall(k, lo, n, a[k] == 7))
  post(forall(k, 0, lo, a[k] == old(a[k])))
{
  fill(a + lo, n - lo);
}
// CHECK-DAG: Verified: fill_tail

int first_x(const point *p, int n)
  pre(valid(p, n) && n >= 1)
{
  return p->x;
}
// CHECK-DAG: Verified: first_x

int past_end(const int *a, int n)
  pre(valid(a, n) && n >= 1)
{
  return a[n];
}
// CHECK-DAG: error: verification failed: past_end [{{.*}}::bounds@[[@LINE-2]]:10]

// A user-declared valid works the same way.
spec bool valid(const long *p, int n) { return true; }

long last(const long *a, int n)
  pre(valid(a, n) && n >= 1)
{
  return a[n - 1];
}
// CHECK-DAG: Verified: last
