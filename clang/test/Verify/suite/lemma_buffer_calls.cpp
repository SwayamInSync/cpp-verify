// RUN: not %cpp-verify --timeout=10000 %s 2>&1 | FileCheck %s
//
// Executable code calls lemmas about its buffers. A proof function is
// outside the object model, so its preconditions state abstract validity;
// the caller gives it by the slice's containment in one of its own objects:
// a declared extent, or the one object a pointer without one addresses.

#include <cppverify.h>
using cppverify::valid;

proof void pair_ordered(const int *a, int n, int i, int j)
  pre(valid(a, n) && n <= 1000 && 0 <= i && i <= j && j < n)
  pre(forall(k, 0, n - 1, a[k] <= a[k + 1]))
  post(a[i] <= a[j])
  decreases(j - i)
{
  if (i < j)
    pair_ordered(a, n, i, j - 1);
}

void last_is_largest(const int *a, int n)
  pre(valid(a, n) && 1 <= n && n <= 1000)
  pre(forall(k, 0, n - 1, a[k] <= a[k + 1]))
{
  contract_assert(forall(k, 0, n, a[k] <= a[n - 1])) by {
    pair_ordered(a, n, k, n - 1);
  }
}
// CHECK-DAG: Verified: last_is_largest

proof void reads(const int *a, int n) pre(valid(a, n) && n >= 1) {}

void too_long(const int *a, int n)
  pre(valid(a, n) && 1 <= n && n <= 1000)
{
  ghost { reads(a, n + 1); }
}
// CHECK-DAG: error: verification failed: too_long {{.*}}bounds

// A pointer without an extent addresses one object.
void one_object(const int *b)
{
  ghost { reads(b, 1); }
}
// CHECK-DAG: Verified: one_object

void two_of_one(const int *b)
{
  ghost { reads(b, 2); }
}
// CHECK-DAG: error: verification failed: two_of_one {{.*}}bounds

void past_the_object(const int *b)
{
  ghost { reads(b + 1, 1); }
}
// CHECK-DAG: error: verification failed: past_the_object {{.*}}bounds
