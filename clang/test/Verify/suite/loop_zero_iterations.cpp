// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s
// RUN: %cpp-verify --lower-only --dump-ir=2 %s -- 2>&1 | FileCheck %s --check-prefix=DUMP
//
// A loop whose condition is the constant false never repeats its body: it
// needs no measure, and the state after it is the state before it.

int wf(int x)
  cppverify::pre(0 <= x && x <= 100)
  cppverify::post(cppverify::result == x)
{
  int r = x;
  while (false) {
    r = r + 1;
  }
  return r;
}
// CHECK-DAG: Verified: wf [backend=z3]

#define SWAP_INT(a, b) do { int t_ = (a); (a) = (b); (b) = t_; } while (0)

int swapped_diff(int x, int y)
  cppverify::pre(0 <= x && x <= 100 && 0 <= y && y <= 100)
  cppverify::post(cppverify::result == y - x)
{
  int a = x;
  int b = y;
  SWAP_INT(a, b);
  return a - b;
}
// CHECK-DAG: Verified: swapped_diff [backend=z3]

int for_false(int x)
  cppverify::pre(0 <= x && x <= 100)
  cppverify::post(cppverify::result == x)
{
  int r = x;
  for (int i = 0; false; i = i + 1)
    r = r + i;
  return r;
}
// CHECK-DAG: Verified: for_false [backend=z3]

// Any other loop is described by its invariant, also where it does not run.
int entry_false(int x)
  cppverify::pre(0 <= x && x <= 100)
  cppverify::post(cppverify::result == x + 5)
{
  int i = 5;
  while (i < 3)
    cppverify::decreases(3 - i)
  {
    i = i + 1;
  }
  return x + i;
}
// CHECK-DAG: error: verification failed: entry_false

int runs_twice(int x)
  cppverify::pre(0 <= x && x <= 100)
  cppverify::post(cppverify::result == x + 2)
{
  int r = x;
  int i = 0;
  while (i < 2)
    cppverify::decreases(2 - i)
  {
    r = r + 1;
    i = i + 1;
  }
  return r;
}
// CHECK-DAG: error: verification failed: runs_twice

// And a measure, when its condition is not the constant false.
int unmeasured(int n)
  cppverify::pre(0 <= n && n <= 100)
  cppverify::post(cppverify::result == n)
{
  int i = 0;
  while (i < n)
    cppverify::invariant(0 <= i && i <= n)
  {
    i = i + 1;
  }
  return i;
}
// CHECK-DAG: Unresolved: unmeasured [backend=z3] [reason=decreases.missing]

cppverify::proof int ghost_never(int n)
  cppverify::pre(0 <= n && n <= 100)
  cppverify::post(cppverify::result == n)
{
  int k = n;
  while (false) {
    k = k + 1;
  }
  return k;
}
// CHECK-DAG: Verified: ghost_never [backend=z3]

// The variables the loop modifies keep their values.
// DUMP-LABEL: passive wf
// DUMP:      {{^ *}}false{{$}}
// DUMP-NEXT: {{^ *}}=={{$}}
// DUMP-NEXT: {{^ *}}r_2{{$}}
// DUMP-NEXT: {{^ *}}r_1{{$}}
