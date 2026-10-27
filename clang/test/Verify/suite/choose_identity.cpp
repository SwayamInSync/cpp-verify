// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s --implicit-check-not=Verified:
//
// A choice is a function of the values its condition reads: two chooses with
// the same condition, up to the name of the bound variable, are one choice,
// as Verus shares one closure function, and a write to a cell the condition
// does not read keeps it.

namespace cv = cppverify;
using namespace cppverify;

cv::proof void same(int n)
  cv::post(cv::choose(k, k > n) == cv::choose(k, k > n))
{
}
// CHECK-DAG: Verified: same [backend=z3]

cv::proof void renamed(int n)
  cv::post(cv::choose(k, k > n) == cv::choose(j, j > n))
{
}
// CHECK-DAG: Verified: renamed [backend=z3]

// A quantifier inside the condition is compared up to its variable too.
cv::proof void same_inner()
  cv::post(cv::choose(k, 0, 10, cv::forall(j, 0, k, j < 5)) ==
           cv::choose(k, 0, 10, cv::forall(i, 0, k, i < 5)))
{
}
// CHECK-DAG: Verified: same_inner [backend=z3]

int same_in_ghost(int n)
  cv::post(cv::result == n)
{
  cv::ghost {
    int a = cv::choose(k, 0, 10, k == 3);
    int b = cv::choose(i, 0, 10, i == 3);
    cv::check(a == b);
  }
  return n;
}
// CHECK-DAG: Verified: same_in_ghost [backend=z3]

// Another condition, another value, or another range is another choice.
cv::proof void other_condition(int n)
  cv::post(cv::choose(k, k > n) == cv::choose(k, k >= n))
{
}
// CHECK-DAG: error: verification failed: other_condition [{{.*}}] (counterexample:

cv::proof void other_value(int n, int m)
  cv::post(cv::choose(k, k > n) == cv::choose(k, k > m))
{
}
// CHECK-DAG: error: verification failed: other_value [{{.*}}] (counterexample:

cv::proof void other_range()
  cv::post(cv::choose(k, 0, 10, k >= 0) == cv::choose(k, 0, 11, k >= 0))
{
}
// CHECK-DAG: error: verification failed: other_range [{{.*}}] [backend=z3] [reason=counterexample]

// The condition reads a[0] to a[n - 1]; b is another object.
void write_other(const int *a, int n, int *b, int x)
  cv::pre(valid(a, n) && n >= 1 && n <= 100 && valid(b, 1))
  cv::modifies(*b)
  cv::post(cv::choose(k, 0, n, a[k] == x) ==
           cv::old(cv::choose(k, 0, n, a[k] == x)))
{
  *b = 5;
}
// CHECK-DAG: Verified: write_other [backend=z3]

void clear(int *b)
  cv::pre(valid(b, 1))
  cv::modifies(*b)
  cv::post(*b == 0)
{
  *b = 0;
}
// CHECK-DAG: Verified: clear [backend=z3]

void call_writes_other(const int *a, int n, int *b, int x)
  cv::pre(valid(a, n) && n >= 1 && n <= 100 && valid(b, 1))
  cv::modifies(*b)
  cv::post(cv::choose(k, 0, n, a[k] == x) ==
           cv::old(cv::choose(k, 0, n, a[k] == x)))
{
  clear(b);
}
// CHECK-DAG: Verified: call_writes_other [backend=z3]

// A write to a cell the condition reads may change the choice.
void write_inside(int *a, int n, int x)
  cv::pre(valid(a, n) && n >= 1 && n <= 100)
  cv::modifies(a[0])
  cv::post(cv::choose(k, 0, n, a[k] == x) ==
           cv::old(cv::choose(k, 0, n, a[k] == x)))
{
  a[0] = x == 0 ? 1 : 0;
}
// CHECK-DAG: error: verification failed: write_inside [{{.*}}] (counterexample:

// Which cells c[a[k]] reads depends on memory too: each read compares what it
// reads in each memory, its address included, so the write to b keeps it.
void write_other_indirect(const int *a, const int *c, int n, int *b, int x)
  cv::pre(valid(a, n) && valid(c, n) && n >= 1 && n <= 100 && valid(b, 1))
  cv::pre(cv::forall(k, 0, n, 0 <= a[k] && a[k] < n))
  cv::modifies(*b)
  cv::post(cv::choose(k, 0, n, c[a[k]] == x) ==
           cv::old(cv::choose(k, 0, n, c[a[k]] == x)))
{
  *b = 5;
}
// CHECK-DAG: Verified: write_other_indirect [backend=z3]
