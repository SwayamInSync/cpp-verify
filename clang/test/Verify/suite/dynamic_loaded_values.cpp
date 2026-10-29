// RUN: %cpp-verify --timeout=20000 %s -- 2>&1 | FileCheck %s
// RUN: not %cpp-verify %s -- -DPOINTER_OPERATIONS 2>&1 | FileCheck %s --check-prefix=POINTER
// RUN: %cpp-verify %s -- -DGLOBAL_TABLE 2>&1 | FileCheck %s --check-prefix=GLOBAL --implicit-check-not=dynamic-storage
//
// A value read through a pointer from new is an integer like any other:
// only the pointer's own address takes part in pointer arithmetic, ordering,
// subscripts, copies, and calls.

#if !defined(POINTER_OPERATIONS) && !defined(GLOBAL_TABLE)
int arithmetic(int a)
  cppverify::pre(-100 < a && a < 100)
  cppverify::post(cppverify::result == 2 * a)
{
  int *p = new int(a);
  int r = *p + 1;
  int s = 1 + *p - 1;
  delete p;
  return r + s - 1;
}
// CHECK-DAG: Verified: arithmetic

bool comparison(int a)
  cppverify::pre(-100 < a && a < 100)
  cppverify::post(cppverify::result == (a < 50 && a <= 60 && !(a > 70) && !(a >= 80)))
{
  int *p = new int(a);
  bool r = *p < 50 && *p <= 60 && !(*p > 70) && !(*p >= 80);
  delete p;
  return r;
}
// CHECK-DAG: Verified: comparison

int two_objects(int a, int b)
  cppverify::pre(-100 < a && a < 100 && -100 < b && b < 100)
  cppverify::post(cppverify::result == a + b)
{
  int *p = new int(a);
  int *q = new int(b);
  int r = *p + *q;
  delete q;
  delete p;
  return r;
}
// CHECK-DAG: Verified: two_objects

cppverify::spec int sq(int x) { return x * x; }

int spec_argument(int a)
  cppverify::pre(-100 < a && a < 100)
  cppverify::post(cppverify::result == a)
{
  int *p = new int(a);
  cppverify::check(sq(*p) == a * a);
  int r = *p;
  delete p;
  return r;
}
// CHECK-DAG: Verified: spec_argument
#endif

#ifdef POINTER_OPERATIONS
int step(int a)
  cppverify::post(cppverify::result == 0)
{
  int *p = new int(a);
  int k = p + 1 == nullptr;
  delete p;
  return 0;
}
// POINTER-DAG: error: step: arithmetic on dynamic-storage pointers is unsupported

bool order(int a)
  cppverify::post(cppverify::result || !cppverify::result)
{
  int *p = new int(a);
  int *q = new int(a);
  bool r = p < q;
  delete q;
  delete p;
  return r;
}
// POINTER-DAG: error: order: ordering dynamic-storage pointers is unsupported
#endif

#ifdef GLOBAL_TABLE
int table[3] = {10, 20, 30};

int global_index(int a)
  cppverify::pre(0 <= a && a < 3)
{
  int *p = new int(a);
  int r = table[*p];
  const int *q = table + *p;
  delete p;
  return r;
}
// GLOBAL: Verified: global_index
#endif
