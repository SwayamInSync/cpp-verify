// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s
//
// C++17 [expr.add]/5: if both operands of a pointer difference are null, the
// result is 0; otherwise both must point into one array object.

// An empty extent permits a null pointer.
long same_empty(const int *a, int n)
  cppverify::pre(cppverify::valid(a, n) && n == 0)
  cppverify::post(cppverify::result == 0)
{
  const int *b = a;
  return b - a;
}
// CHECK-DAG: Verified: same_empty [backend=z3]

long both_null()
  cppverify::post(cppverify::result == 0)
{
  const int *p = nullptr;
  const int *q = nullptr;
  return p - q;
}
// CHECK-DAG: Verified: both_null [backend=z3]

// The pointer a loop advances, measured from its start, with n == 0 allowed.
long walked(const int *a, int n)
  cppverify::pre(cppverify::valid(a, n) && n >= 0 && n <= 1000)
  cppverify::post(cppverify::result == n)
{
  const int *q = a;
  int i = 0;
  while (i < n)
    cppverify::invariant(0 <= i && i <= n && q == a + i)
    cppverify::decreases(n - i)
  {
    q = q + 1;
    i = i + 1;
  }
  return q - a;
}
// CHECK-DAG: Verified: walked [backend=z3]

// Null minus a pointer into an object is undefined.
long null_minus_object(const int *a, int n)
  cppverify::pre(cppverify::valid(a, n) && n >= 1)
{
  const int *z = nullptr;
  return a - z;
}
// CHECK-DAG: :{{[0-9]+:[0-9]+}}: error: verification failed: null_minus_object [pointer-difference] {{.*}}[reason=counterexample]

// Either may be null while the other is not.
long one_null(const int *a, const int *b)
  cppverify::aliases(a, b)
{
  return a - b;
}
// CHECK-DAG: :{{[0-9]+:[0-9]+}}: error: verification failed: one_null [pointer-difference] {{.*}}[reason=counterexample]
