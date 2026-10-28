// RUN: not %cpp-verify --jobs=1 %s -- 2>&1 | FileCheck %s
//
// A callee's footprint lies in the caller's frame when its cells do,
// whichever pointer reaches them. Before, a callee region of one scalar
// object never lay in a caller cell, and a region reached through a copy
// (q = a + 2) never lay in the caller's region of a, so these calls failed
// their frame check although they wrote only what the caller may write.

void set(int *p, int v)
  cppverify::pre(p != nullptr)
  cppverify::modifies(*p)
  cppverify::post(*p == v)
{
  *p = v;
}
// CHECK-DAG: Verified: set [backend=z3]

void zero2(int *p, int n)
  cppverify::pre(cppverify::valid(p, n) && n >= 2)
  cppverify::modifies(p[0 : 2])
  cppverify::post(p[0] == 0 && p[1] == 0)
{
  p[0] = 0;
  p[1] = 0;
}
// CHECK-DAG: Verified: zero2 [backend=z3]

// The callee's region is the one cell the caller may write.
void cell_frame(int *p)
  cppverify::pre(p != nullptr)
  cppverify::modifies(p[0])
  cppverify::post(*p == 5)
{
  set(p, 5);
}
// CHECK-DAG: Verified: cell_frame [backend=z3]

void element_frame(int *a)
  cppverify::pre(cppverify::valid(a, 4))
  cppverify::modifies(a[2])
  cppverify::post(a[2] == 5 && a[1] == cppverify::old(a[1]))
{
  set(a + 2, 5);
}
// CHECK-DAG: Verified: element_frame [backend=z3]

// A copy of a pointer into the region's object.
void copy_region(int *a)
  cppverify::pre(cppverify::valid(a, 4))
  cppverify::modifies(*a)
  cppverify::post(a[2] == 5)
{
  int *q = a + 2;
  set(q, 5);
}
// CHECK-DAG: Verified: copy_region [backend=z3]

void copy_range(int *a)
  cppverify::pre(cppverify::valid(a, 4))
  cppverify::modifies(*a)
  cppverify::post(a[2] == 0 && a[3] == 0)
{
  int *q = a + 2;
  zero2(q, 2);
}
// CHECK-DAG: Verified: copy_range [backend=z3]

void chosen_region(int *a, int *b, bool c)
  cppverify::pre(cppverify::valid(a, 4) && cppverify::valid(b, 4))
  cppverify::modifies(*a, *b)
{
  int *q = c ? a + 1 : b + 3;
  set(q, 5);
}
// CHECK-DAG: Verified: chosen_region [backend=z3]

void clear(int *p, int n)
  cppverify::pre(cppverify::valid(p, n))
  cppverify::modifies(p[0 : n])
{
  for (int i = 0; i < n; i = i + 1)
    cppverify::invariant(0 <= i && i <= n)
    cppverify::modifies(p[0 : n])
    cppverify::decreases(n - i)
  {
    p[i] = 0;
  }
}
// CHECK-DAG: Verified: clear [backend=z3]

// An empty range writes nothing, wherever it starts.
void empty_elsewhere(int *a, int *b)
  cppverify::pre(cppverify::valid(a, 4) && cppverify::valid(b, 4))
  cppverify::modifies(*a)
{
  int *q = b + 4;
  clear(q, 0);
}
// CHECK-DAG: Verified: empty_elsewhere [backend=z3]

// The neighbor of the cell the caller may write.
void neighbor_cell(int *a)
  cppverify::pre(cppverify::valid(a, 4))
  cppverify::modifies(a[2])
{
  set(a + 3, 5);
}
// CHECK-DAG: :[[@LINE-2]]:3: error: verification failed: neighbor_cell [frame]

// A copy into another parameter's object, outside the caller's region.
void other_object(int *a, int *b)
  cppverify::pre(cppverify::valid(a, 4) && cppverify::valid(b, 4))
  cppverify::modifies(*a)
{
  int *q = b + 1;
  set(q, 5);
}
// CHECK-DAG: :[[@LINE-2]]:3: error: verification failed: other_object [frame]

// The copy starts inside a's object only if b lay below it.
void other_object_above(int *a, int *b)
  cppverify::pre(cppverify::valid(a, 4) && cppverify::valid(b, 4) && a + 4 <= b)
  cppverify::modifies(*a)
{
  int *q = b + 1;
  set(q, 5);
}
// CHECK-DAG: :[[@LINE-2]]:3: error: verification failed: other_object_above [frame]

// A callee may name more cells than its extent: these run past a's object.
void wide(int *p)
  cppverify::pre(cppverify::valid(p, 1))
  cppverify::modifies(p[0 : 3])
{
  p[0] = 1;
}
// CHECK-DAG: Verified: wide [backend=z3]

void wide_past(int *a)
  cppverify::pre(cppverify::valid(a, 4))
  cppverify::modifies(*a)
{
  int *q = a + 3;
  wide(q);
}
// CHECK-DAG: :[[@LINE-2]]:3: error: verification failed: wide_past [frame]

// When c is false the cell is in b, which the caller may not write.
void chosen_outside(int *a, int *b, bool c)
  cppverify::pre(cppverify::valid(a, 4) && cppverify::valid(b, 4))
  cppverify::modifies(*a)
{
  int *q = c ? a + 1 : b + 3;
  set(q, 5);
}
// CHECK-DAG: :[[@LINE-2]]:3: error: verification failed: chosen_outside [frame]
// CHECK-DAG: note: counterexample: {{.*}}c = false{{( ->|,|$)}}

// The cell before the object, where its end would still be inside.
[[cppverify::trusted]] int *before(const int *a, int n)
  cppverify::pre(cppverify::valid(a, n) && n >= 1)
  cppverify::post(cppverify::result != nullptr && cppverify::result + 1 == a);
// CHECK-DAG: Trusted: before

void before_object(int *a)
  cppverify::pre(cppverify::valid(a, 4))
  cppverify::modifies(*a)
{
  int *q = before(a, 4);
  set(q, 5);
}
// CHECK-DAG: :[[@LINE-2]]:3: error: verification failed: before_object [frame]

// The range a[3 : 2] runs past the cell a[3] the caller may write.
void range_past_cell(int *a)
  cppverify::pre(cppverify::valid(a, 5))
  cppverify::modifies(a[3])
{
  int *q = a + 3;
  zero2(q, 2);
}
// CHECK-DAG: :[[@LINE-2]]:3: error: verification failed: range_past_cell [frame]
