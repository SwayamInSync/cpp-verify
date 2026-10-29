// RUN: not %cpp-verify --jobs=1 %s -- -std=c++20 > %t 2>&1
// RUN: FileCheck %s < %t
// RUN: FileCheck %s --check-prefix=SOUND < %t
// RUN: not %cpp-verify --jobs=1 --backend=bmc --unroll=5 %s -- -std=c++20 2>&1 | FileCheck %s --check-prefix=BMC
// RUN: not %cpp-verify --lower-only --dump-ir=1 %s -- -std=c++20 2>&1 | FileCheck %s --check-prefix=VCR
//
// A range-based for loop over an array visits its elements in order: its
// variable is each element, a copy or a reference. Its contract names the
// position, cppverify::index, the number of elements before the current one
// (from 0 to the size); without a measure, it decreases the elements left.
// Every correct function has a wrong twin that must be refuted.
//
// No proof here holds only because no execution reaches its end.
// SOUND-NOT: vacuous

namespace cv = cppverify;

int sum3()
  cv::post(cv::result == 6)
{
  int a[3] = {1, 2, 3};
  int s = 0;
  for (int v : a)
    cv::invariant(s == (cv::index == 0 ? 0 : cv::index == 1 ? 1 : cv::index == 2 ? 3 : 6))
    s = s + v;
  return s;
}
// CHECK-DAG: Verified: sum3 [backend=z3]

int sum3_wrong()
  cv::post(cv::result == 7)
{
  int a[3] = {1, 2, 3};
  int s = 0;
  for (int v : a)
    cv::invariant(s == (cv::index == 0 ? 0 : cv::index == 1 ? 1 : cv::index == 2 ? 3 : 6))
    s = s + v;
  return s;
}
// CHECK-DAG: error: verification failed: sum3_wrong [postcondition]{{.*}}[reason=counterexample]

// A reference writes the element.
int zeroed()
  cv::post(cv::result == 0)
{
  int a[4] = {5, 6, 7, 8};
  for (int &x : a)
    cv::invariant(cv::forall(k, 0, cv::index, a[k] == 0))
    x = 0;
  return a[0] + a[1] + a[2] + a[3];
}
// CHECK-DAG: Verified: zeroed [backend=z3]

int zeroed_wrong()
  cv::post(cv::result == 0)
{
  int a[4] = {5, 6, 7, 8};
  for (int x : a)
    cv::invariant(true)
    x = 0;
  return a[0];
}
// CHECK-DAG: error: verification failed: zeroed_wrong [postcondition]{{.*}}[reason=counterexample]

// An array member through a pointer, with a bound that needs the position.
struct Ring {
  int buf[8];
  int head;
};

int total(const Ring *r)
  cv::pre(r != nullptr)
  cv::pre(cv::forall(k, 0, 8, 0 <= r->buf[k] && r->buf[k] <= 10))
  cv::post(0 <= cv::result && cv::result <= 80)
{
  int s = 0;
  for (const int &v : r->buf)
    cv::invariant(0 <= s && s <= 10 * cv::index)
    s = s + v;
  return s;
}
// CHECK-DAG: Verified: total [backend=z3]

int total_wrong(const Ring *r)
  cv::pre(r != nullptr)
  cv::pre(cv::forall(k, 0, 8, 0 <= r->buf[k] && r->buf[k] <= 10))
  cv::post(cv::result <= 70)
{
  int s = 0;
  for (int v : r->buf)
    cv::invariant(0 <= s && s <= 10 * cv::index)
    s = s + v;
  return s;
}
// CHECK-DAG: error: verification failed: total_wrong [postcondition]{{.*}}[reason=counterexample]

void clear(Ring *r)
  cv::pre(r != nullptr)
  cv::modifies(r->buf[0 : 8])
  cv::post(cv::forall(k, 0, 8, r->buf[k] == 0))
{
  for (int &x : r->buf)
    cv::invariant(cv::forall(k, 0, cv::index, r->buf[k] == 0))
    x = 0;
}
// CHECK-DAG: Verified: clear [backend=z3]

// Binding a reference to an element requires the element, used or not.
int count_elements(Ring *r)
  cv::pre(r != nullptr)
  cv::post(cv::result == 8)
{
  int n = 0;
  for (int &x : r->buf)
    cv::invariant(n == cv::index)
    n = n + 1;
  return n;
}
// CHECK-DAG: Verified: count_elements [backend=z3]

int count_elements_wrong(Ring *r)
  cv::post(cv::result == 8)
{
  int n = 0;
  for (int &x : r->buf)
    cv::invariant(n == cv::index)
    n = n + 1;
  return n;
}
// CHECK-DAG: :[[@LINE-5]]:3: error: verification failed: count_elements_wrong [dereference] {{.*}}[reason=counterexample]
// CHECK-DAG: note: counterexample: {{.*}}r = 0{{( ->|,|$)}}

// A constant table, break, continue, and a conversion to the variable's
// type.
constexpr int Primes[5] = {2, 3, 5, 7, 11};

long first_above(int bound)
  cv::post(cv::result == -1 || cv::result > bound)
  cv::post(cv::result != -1 || cv::forall(k, 0, 5, Primes[k] <= bound))
{
  long found = -1;
  for (long p : Primes)
    cv::invariant(found == -1)
    cv::invariant(cv::forall(k, 0, cv::index, Primes[k] <= bound))
  {
    if (p <= bound)
      continue;
    found = p;
    break;
  }
  return found;
}
// CHECK-DAG: Verified: first_above [backend=z3]

long first_above_wrong(int bound)
  cv::post(cv::result > bound)
{
  long found = -1;
  for (long p : Primes)
    cv::invariant(found == -1)
    cv::invariant(cv::forall(k, 0, cv::index, Primes[k] <= bound))
  {
    if (p <= bound)
      continue;
    found = p;
    break;
  }
  return found;
}
// CHECK-DAG: error: verification failed: first_above_wrong {{.*}}[reason=counterexample]
// CHECK-DAG: note: counterexample: {{.*}}bound = {{[0-9]+}}{{( ->|,|$)}}

// The elements are read in each iteration; the range is located once.
int doubled()
  cv::post(cv::result == 12)
{
  int a[3] = {1, 2, 3};
  int s = 0;
  for (int v : a)
    cv::invariant(cv::forall(k, cv::index, 3, a[k] == k + 1))
    cv::invariant(s == (cv::index == 0 ? 0 : cv::index == 1 ? 2 : cv::index == 2 ? 6 : 12))
    s = s + 2 * v;
  return s;
}
// CHECK-DAG: Verified: doubled [backend=z3]

// In a template, cppverify::index is instantiated with its loop.
template <typename T>
T sum_of_three()
  cv::post(cv::result == 6)
{
  T a[3] = {1, 2, 3};
  T s = 0;
  for (T v : a)
    cv::invariant(s == (cv::index == 0 ? 0 : cv::index == 1 ? 1 : cv::index == 2 ? 3 : 6))
    s = s + v;
  return s;
}

long use_sum_of_three()
  cv::post(cv::result == 6)
{
  long r = sum_of_three<long>();
  return r;
}
// CHECK-DAG: Verified: sum_of_three<long> [backend=z3]
// CHECK-DAG: Verified: use_sum_of_three [backend=z3]

// A loop over a loop, an init statement, a string literal (whose last
// element is its terminating zero), and Booleans.
int nested()
  cv::post(cv::result == 9)
{
  int a[2] = {1, 2};
  int b[3] = {1, 1, 1};
  int s = 0;
  for (int x : a)
    cv::invariant(s == 3 * (cv::index == 0 ? 0 : cv::index == 1 ? 1 : 3))
    for (int y : b)
      cv::invariant(s == 3 * (x == 1 ? 0 : 1) + x * cv::index)
      s = s + x * y;
  return s;
}
// CHECK-DAG: Verified: nested [backend=z3]

int nested_wrong()
  cv::post(cv::result == 6)
{
  int a[2] = {1, 2};
  int b[3] = {1, 1, 1};
  int s = 0;
  for (int x : a)
    cv::invariant(s == 3 * (cv::index == 0 ? 0 : cv::index == 1 ? 1 : 3))
    for (int y : b)
      cv::invariant(s == 3 * (x == 1 ? 0 : 1) + x * cv::index)
      s = s + x * y;
  return s;
}
// CHECK-DAG: error: verification failed: nested_wrong [postcondition]{{.*}}[reason=counterexample]

int with_init()
  cv::post(cv::result == 6)
{
  int s = 0;
  for (int a[3] = {1, 2, 3}; int v : a)
    cv::invariant(s == (cv::index == 0 ? 0 : cv::index == 1 ? 1 : cv::index == 2 ? 3 : 6))
    s = s + v;
  return s;
}
// CHECK-DAG: Verified: with_init [backend=z3]

int letters()
  cv::post(cv::result == 3)
{
  int n = 0;
  for (char c : "abc")
    cv::invariant(n == (cv::index < 3 ? cv::index : 3))
    if (c != 0)
      n = n + 1;
  return n;
}
// CHECK-DAG: Verified: letters [backend=z3]

int letters_wrong()
  cv::post(cv::result == 4)
{
  int n = 0;
  for (char c : "abc")
    cv::invariant(n == (cv::index < 3 ? cv::index : 3))
    if (c != 0)
      n = n + 1;
  return n;
}
// CHECK-DAG: error: verification failed: letters_wrong [postcondition]{{.*}}[reason=counterexample]

bool any_set()
  cv::post(cv::result)
{
  bool f[3] = {false, true, false};
  bool r = false;
  for (bool b : f)
    cv::invariant(r == (cv::index >= 2))
    r = r || b;
  return r;
}
// CHECK-DAG: Verified: any_set [backend=z3]

bool any_set_wrong()
  cv::post(!cv::result)
{
  bool f[3] = {false, true, false};
  bool r = false;
  for (bool b : f)
    cv::invariant(r == (cv::index >= 2))
    r = r || b;
  return r;
}
// CHECK-DAG: error: verification failed: any_set_wrong [postcondition]{{.*}}[reason=counterexample]

// An array member of a local record, records bound by reference, and the
// user's measure.
struct Bucket {
  int items[3];
};

int local_member()
  cv::post(cv::result == 6)
{
  Bucket b;
  b.items[0] = 1;
  b.items[1] = 2;
  b.items[2] = 3;
  int s = 0;
  for (int v : b.items)
    cv::invariant(s == (cv::index == 0 ? 0 : cv::index == 1 ? 1 : cv::index == 2 ? 3 : 6))
    cv::invariant(b.items[0] == 1 && b.items[1] == 2 && b.items[2] == 3)
    s = s + v;
  return s;
}
// CHECK-DAG: Verified: local_member [backend=z3]

struct Pt {
  int x;
  int y;
};

int sum_x()
  cv::post(cv::result == 4)
{
  Pt pts[2] = {{1, 2}, {3, 4}};
  int s = 0;
  for (const Pt &p : pts)
    cv::invariant(s == (cv::index == 0 ? 0 : cv::index == 1 ? 1 : 4))
    s = s + p.x;
  return s;
}
// CHECK-DAG: Verified: sum_x [backend=z3]

int sum_x_wrong()
  cv::post(cv::result == 6)
{
  Pt pts[2] = {{1, 2}, {3, 4}};
  int s = 0;
  for (const Pt &p : pts)
    cv::invariant(s == (cv::index == 0 ? 0 : cv::index == 1 ? 1 : 4))
    s = s + p.x;
  return s;
}
// CHECK-DAG: error: verification failed: sum_x_wrong [postcondition]{{.*}}[reason=counterexample]

int measured()
  cv::post(true)
{
  int a[3] = {1, 1, 1};
  int s = 0;
  for (int v : a)
    cv::decreases(3 - cv::index)
    s = v;
  return s;
}
// CHECK-DAG: Verified: measured [backend=z3]

int measured_wrong()
  cv::post(true)
{
  int a[3] = {1, 1, 1};
  int s = 0;
  for (int v : a)
    cv::decreases(cv::index)
    s = v;
  return s;
}
// CHECK-DAG: error: verification failed: measured_wrong [termination]{{.*}}[reason=counterexample]

int may_diverge()
  cv::post(true)
{
  int a[3] = {1, 1, 1};
  int s = 0;
  for (int v : a)
    cv::decreases(*)
    s = v;
  return s;
}
// CHECK-DAG: Verified: may_diverge [backend=z3] [partial]

// The contract holds at the head, where the loop variable is not declared.
int names_variable()
  cv::post(true)
{
  int a[2] = {1, 2};
  int s = 0;
  for (int v : a)
    cv::invariant(v >= 0)
    s = v;
  return s;
}
// CHECK-DAG: range_for.cpp:[[@LINE-5]]:3: error: names_variable: the contract of a range-based for loop cannot name its variable, which each iteration declares; name the element with cppverify::index

// A global array is an object like a local one.
int Counts[4] = {1, 2, 3, 4};

int over_global()
  cv::post(true)
{
  int s = 0;
  for (int v : Counts)
    s = v;
  return s;
}
// CHECK-DAG: Verified: over_global

// Not supported: a range that may move, a range over a class, and an array
// of arrays.

int first_column()
  cv::post(true)
{
  int g[2][2] = {{1, 2}, {3, 4}};
  int s = 0;
  for (auto row : g)
    s = row[0];
  return s;
}
// CHECK-DAG: range_for.cpp:[[@LINE-4]]:3: error: first_column: a range-based for loop over an array of arrays is unsupported; index it

int moving(Ring *r, Ring *other)
  cv::pre(r != nullptr && other != nullptr)
  cv::post(true)
{
  int s = 0;
  for (int v : r->buf) {
    s = v;
    r = other;
  }
  return s;
}
// CHECK-DAG: range_for.cpp:[[@LINE-6]]:3: error: moving: the range of this loop is located through a call, a pointer read from memory, or a variable its body may change; locate it through a variable the body does not change

[[cppverify::trusted]] Ring *self(Ring *r)
  cv::pre(r != nullptr)
  cv::post(cv::result == r);

int through_call(Ring *r)
  cv::pre(r != nullptr)
  cv::post(true)
{
  int s = 0;
  for (int v : self(r)->buf)
    s = v;
  return s;
}
// CHECK-DAG: range_for.cpp:[[@LINE-4]]:3: error: through_call: the range of this loop is located through a call, a pointer read from memory, or a variable its body may change; locate it through a variable the body does not change

[[cppverify::trusted]] int which(int x)
  cv::post(0 <= cv::result && cv::result < 2);

int row_through_call(int x)
  cv::post(true)
{
  int g[2][3] = {{1, 2, 3}, {4, 5, 6}};
  int s = 0;
  for (int v : g[which(x)])
    s = v;
  return s;
}
// CHECK-DAG: range_for.cpp:[[@LINE-4]]:3: error: row_through_call: the range of this loop is located through a call, a pointer read from memory, or a variable its body may change; locate it through a variable the body does not change

struct Bag {
  int items[2];
  const int *begin() const { return items; }
  const int *end() const { return items + 2; }
};

int bag_total(const Bag *b)
  cv::pre(b != nullptr)
  cv::post(true)
{
  int s = 0;
  for (int v : *b)
    s = v;
  return s;
}
// CHECK-DAG: range_for.cpp:[[@LINE-4]]:3: error: bag_total: a range-based for loop over a class (through its begin and end) is unsupported; loop over an array, or index the class

// BMC: Verified: sum3 [backend=bmc, bound=3]
// BMC: error: verification failed: sum3_wrong

// VCR-LABEL: fn sum3
// VCR:         assign __index_[[ID:[0-9]+]]
// VCR-NEXT:      0
// VCR-NEXT:    while
// VCR-NEXT:      <
// VCR-NEXT:        __index_[[ID]]
// VCR-NEXT:        3
