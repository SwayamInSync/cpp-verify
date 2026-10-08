// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefixes=CHECK,DEDUCTIVE
// RUN: not %cpp-verify --backend=bmc --unroll=2 %s 2>&1 | FileCheck %s
//
// Memory checking is on by default. A pointer parameter addresses its
// declared valid(p, n) extent, or else a single object; every access and
// every pointer step must stay within the object its pointer comes from, one
// past the end allowed for a step. Copies, conditional selections, and
// rebinding keep the check, element pointers pass to callees, and a pointer a
// callee returns is a valid object of its own.

cppverify::spec bool valid(int *p, int n) { return true; }
cppverify::spec bool valid(const int *p, int n) { return true; }

int beyond_single(const int *p)
  cppverify::pre(p != nullptr)
{
  return p[1];
}
// CHECK-DAG: error: verification failed: beyond_single [{{.*}}::bounds@

int through_copy(const int *p, int n)
  cppverify::pre(valid(p, n) && n >= 1 && n < 100)
{
  const int *q = p;
  return q[n];
}
// CHECK-DAG: error: verification failed: through_copy [{{.*}}::bounds@

int through_selection(const int *p, const int *q, bool c)
  cppverify::pre(p != nullptr && q != nullptr)
{
  const int *r = c ? p : q;
  return r[1];
}
// CHECK-DAG: error: verification failed: through_selection [{{.*}}::bounds@

int after_rebinding(const int *p, int n)
  cppverify::pre(valid(p, n) && n >= 1 && n < 100)
{
  p = p + n;
  return p[0];
}
// CHECK-DAG: error: verification failed: after_rebinding [{{.*}}::bounds@

void loop_overrun(int *p, int n)
  cppverify::pre(valid(p, n) && n >= 1 && n < 100)
  cppverify::modifies(*p)
{
  for (int i = 0; i <= n; i = i + 1)
    cppverify::invariant(0 <= i && i <= n + 1)
    cppverify::decreases(n + 1 - i)
  {
    p[i] = 0;
  }
}
// CHECK-DAG: error: verification failed: loop_overrun [{{.*}}::bounds@

int empty_extent(const int *p, int n)
  cppverify::pre(valid(p, n) && n == 0 && p != nullptr)
{
  return p[0];
}
// CHECK-DAG: error: verification failed: empty_extent [{{.*}}::bounds@

bool step_too_far(const int *p)
  cppverify::pre(valid(p, 2))
{
  const int *q = p + 3;
  return q == p;
}
// CHECK-DAG: error: verification failed: step_too_far [{{.*}}::bounds@

bool one_past(const int *p)
  cppverify::pre(valid(p, 2))
  cppverify::post(cppverify::result)
{
  return p + 2 != p;
}
// CHECK-DAG: Verified: one_past

void set(int *x)
  cppverify::pre(x != nullptr)
  cppverify::modifies(*x)
  cppverify::post(*x == 0)
{
  *x = 0;
}

void clear_all(int *p, int n)
  cppverify::pre(valid(p, n) && n >= 0 && n < 1000)
  cppverify::modifies(*p)
{
  for (int i = 0; i < n; i = i + 1)
    cppverify::invariant(0 <= i && i <= n)
    cppverify::decreases(n - i)
  {
    set(p + i);
  }
}
// DEDUCTIVE-DAG: Verified: clear_all

const int *element(const int *p, int n, int i)
  cppverify::pre(valid(p, n) && 0 <= i && i < n)
  cppverify::post(cppverify::result == p + i)
{
  return p + i;
}

int read_element(const int *p, int n, int i)
  cppverify::pre(valid(p, n) && 0 <= i && i < n && n < 1000)
  cppverify::post(cppverify::result == p[i])
{
  const int *e = element(p, n, i);
  return *e;
}
// CHECK-DAG: Verified: element
// CHECK-DAG: Verified: read_element

[[cppverify::trusted]] int *external_cell(int value)
  cppverify::post(cppverify::result != nullptr)
  cppverify::post(*cppverify::result == value);

int read_external(int value)
  cppverify::post(cppverify::result == value)
{
  int *cell = external_cell(value);
  return *cell;
}
// CHECK-DAG: Verified: read_external

int past_external(int value)
  cppverify::post(true)
{
  int *cell = external_cell(value);
  return cell[1];
}
// CHECK-DAG: error: verification failed: past_external [{{.*}}::bounds@

struct Pair {
  int first;
  int second;
};

// The object after a single object is not part of it, wherever it lies.
int past_object(const Pair *p, const Pair *q)
  cppverify::pre(p != nullptr && q != nullptr && q == p + 1)
{
  return (p + 1)->second;
}
// CHECK-DAG: error: verification failed: past_object [{{.*}}::bounds@
