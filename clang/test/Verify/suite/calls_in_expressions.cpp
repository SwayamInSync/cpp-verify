// RUN: not %cpp-verify --jobs=1 %s -- > %t 2>&1
// RUN: FileCheck %s < %t
// RUN: FileCheck %s --check-prefix=SOUND < %t
// RUN: %cpp-verify --lower-only --dump-ir=1 %s -- 2>&1 | FileCheck %s --check-prefix=VCR
// RUN: not %cpp-verify --jobs=1 %s -- -DORDER 2>&1 | FileCheck %s --check-prefix=ORDER
// RUN: not %cpp-verify --jobs=1 %s -- -std=c++14 2>&1 | FileCheck %s --check-prefix=CXX14
//
// A call of a function with a contract may stand anywhere an expression may:
// it runs where C++ evaluates it, before what reads its result, a condition's
// call before its branch, a short-circuit operand's or a branch's call only
// on its path, and a loop condition's call at every test. C++ leaves the
// order of unsequenced operands open, so a call that may write what another
// operand reads is an error.
//
// No proof here holds only because no execution reaches its end.
// SOUND-NOT: vacuous

namespace cv = cppverify;

int inc(int x)
  cv::pre(x < 1000)
  cv::post(cv::result == x + 1)
{
  return x + 1;
}
// CHECK: Verified: inc

int sq(int x)
  cv::pre(-1000 <= x && x <= 1000)
  cv::post(cv::result == x * x)
{
  return x * x;
}
// CHECK: Verified: sq

bool positive(int x)
  cv::post(cv::result == (x > 0))
{
  return x > 0;
}
// CHECK: Verified: positive

int add_one(int *p)
  cv::pre(p != nullptr && *p < 1000)
  cv::modifies(*p)
  cv::post(*p == cv::old(*p) + 1 && cv::result == *p)
{
  *p = *p + 1;
  return *p;
}
// CHECK: Verified: add_one

bool try_get(int &out, bool ok)
  cv::modifies(out)
  cv::post(!cv::result || out == 5)
{
  if (!ok)
    return false;
  out = 5;
  return true;
}
// CHECK: Verified: try_get

int twice_inc(int x)
  cv::pre(0 <= x && x < 100)
  cv::post(cv::result == 2 * x + 2)
{
  return inc(x) * 2;
}
// CHECK: Verified: twice_inc
// VCR-LABEL: fn twice_inc
// VCR: call inc -> __call_[[T:[0-9]+]]
// VCR-NEXT: x
// VCR-NEXT: return
// VCR-NEXT: *
// VCR-NEXT: __call_[[T]]
// VCR-NEXT: 2

int sum_sq(int a, int b)
  cv::pre(-100 <= a && a <= 100 && -100 <= b && b <= 100)
  cv::post(cv::result == a * a + b * b)
{
  return sq(a) + sq(b);
}
// CHECK: Verified: sum_sq

int nested(int x)
  cv::pre(0 <= x && x < 100)
  cv::post(cv::result == x + 3)
{
  return inc(inc(x)) + 1;
}
// CHECK: Verified: nested

int stored(int *p, int x)
  cv::pre(p != nullptr && 0 <= x && x < 100)
  cv::modifies(*p)
  cv::post(*p == 2 * x + 2 && cv::result == x + 1)
{
  *p = inc(x) * 2;
  int y = 0;
  y += inc(x);
  return y;
}
// CHECK: Verified: stored

int indexed(const int *a, int i)
  cv::pre(cv::valid(a, 4) && 0 <= i && i < 3)
  cv::post(cv::result == a[i + 1])
{
  return a[inc(i)];
}
// CHECK: Verified: indexed

int branch(int x)
  cv::pre(0 <= x && x < 100)
  cv::post(cv::result == (x >= 5 ? 1 : 0))
{
  if (inc(x) > 5)
    return 1;
  return 0;
}
// CHECK: Verified: branch

// The second operand's call runs only where the first holds, so its
// precondition is needed only there.
int guarded(int x)
  cv::pre(-2000 <= x && x <= 2000)
  cv::post(cv::result == (x >= -1000 && x <= 1000 && x * x > 4 ? 1 : 0))
{
  if (x >= -1000 && x <= 1000 && sq(x) > 4)
    return 1;
  return 0;
}
// CHECK: Verified: guarded
// VCR-LABEL: fn guarded
// VCR: assign __path_[[P:[0-9]+]]
// VCR: if
// VCR-NEXT: __path_[[P]]
// VCR-NEXT: call sq -> __call_[[S:[0-9]+]]
// VCR-NEXT: x
// VCR-NEXT: assign __path_[[P]]
// VCR-NEXT: >
// VCR-NEXT: __call_[[S]]
// VCR-NEXT: 4
// VCR-NEXT: if
// VCR-NEXT: __path_[[P]]

int unguarded(int x)
  cv::pre(-2000 <= x && x <= 2000)
{
  if (sq(x) > 4 && x <= 1000)
    return 1;
  return 0;
}
// CHECK: :[[@LINE-4]]:7: error: verification failed: unguarded [precondition]

int either(int x)
  cv::pre(-2000 <= x && x <= 2000)
  cv::post(cv::result == 1 || (-1000 <= x && x <= 1000))
{
  if (x < -1000 || x > 1000 || sq(x) < 0)
    return 1;
  return 0;
}
// CHECK: Verified: either

int choose(bool c, int x)
  cv::pre(0 <= x && x < 100)
  cv::post(cv::result == (c ? x + 1 : x * x))
{
  int y = c ? inc(x) : sq(x);
  return y;
}
// CHECK: Verified: choose

int choose_wrong(bool c, int x)
  cv::pre(0 <= x && x < 2000)
{
  int y = c ? inc(x) : sq(x);
  return y;
}
// CHECK: :[[@LINE-3]]:15: error: verification failed: choose_wrong [precondition]

int count_up(int n)
  cv::pre(0 <= n && n < 100)
  cv::post(cv::result == n)
{
  int i = 0;
  while (inc(i) <= n)
    cv::invariant(0 <= i && i <= n)
    cv::decreases(n - i)
  {
    i = i + 1;
  }
  return i;
}
// CHECK: Verified: count_up
// VCR-LABEL: fn count_up
// VCR: while
// VCR-NEXT: true
// VCR: call inc -> __call_[[C:[0-9]+]]
// VCR-NEXT: i
// VCR-NEXT: if
// VCR-NEXT: !
// VCR-NEXT: <=
// VCR-NEXT: __call_[[C]]
// VCR-NEXT: n
// VCR-NEXT: break

int count_for(int n)
  cv::pre(0 <= n && n < 100)
  cv::post(cv::result == n)
{
  int k = 0;
  for (int i = 0; positive(n - i); i = i + 1)
    cv::invariant(0 <= i && i <= n && k == i)
    cv::decreases(n - i)
  {
    k = k + 1;
  }
  return k;
}
// CHECK: Verified: count_for

int count_do(int n)
  cv::pre(1 <= n && n < 100)
  cv::post(cv::result == n)
{
  int i = 0;
  do {
    i = i + 1;
  } while (inc(i) <= n)
    cv::invariant(1 <= i && i <= n)
    cv::decreases(n - i);
  return i;
}
// CHECK: Verified: count_do

// A loop condition's call is checked at every test.
int count_past(int n)
  cv::pre(0 <= n && n < 2000)
{
  int i = 0;
  while (inc(i) <= n)
    cv::invariant(0 <= i && i <= n)
    cv::decreases(n - i)
  {
    i = i + 1;
  }
  return i;
}
// CHECK: :[[@LINE-8]]:10: error: verification failed: count_past [precondition]

// A call's result is its postcondition's, not any value.
int wrong(int x)
  cv::pre(0 <= x && x < 100)
  cv::post(cv::result == 2 * x)
{
  return inc(x) * 2;
}
// CHECK: error: verification failed: wrong {{.*}}postcondition

// Calls that write nothing another operand reads, in any order.
int reads_and_calls(int *p)
  cv::pre(p != nullptr && -100 <= *p && *p <= 100)
  cv::post(cv::result == *p * *p + *p)
{
  return sq(*p) + *p;
}
// CHECK: Verified: reads_and_calls

int found(bool ok)
  cv::post(cv::result == 5 || cv::result == 0)
{
  int a[1];
  if (try_get(a[0], ok))
    return a[0];
  return 0;
}
// CHECK: Verified: found

struct Counter {
  int n;

  int get() const
    cv::post(cv::result == n)
  {
    return n;
  }

  int bump_get()
    cv::pre(n < 1000)
    cv::modifies(n)
    cv::post(n == cv::old(n) + 1 && cv::result == n)
  {
    n = n + 1;
    return n;
  }
};
// CHECK: Verified: Counter::get
// CHECK: Verified: Counter::bump_get

int doubled(Counter &c)
  cv::pre(-1000 < c.n && c.n < 1000)
  cv::post(cv::result == 2 * c.n)
{
  return c.n + c.get();
}
// CHECK: Verified: doubled

// An uninitialized local the call initializes.
int out_local(bool ok)
  cv::post(cv::result == 5 || cv::result == 0)
{
  int v;
  if (try_get(v, ok))
    return v;
  return 0;
}
// CHECK: Verified: out_local

// The recursive call runs, and lowers the measure, only on its branch.
int depth(int n)
  cv::pre(0 <= n && n < 100)
  cv::post(cv::result == n)
  cv::decreases(n)
{
  return n <= 0 ? 0 : depth(n - 1) + 1;
}
// CHECK: Verified: depth

// Each declarator's call runs after the one before it is initialized.
int two(int x)
  cv::pre(0 <= x && x < 100)
  cv::post(cv::result == x + 2)
{
  int a = inc(x), b = inc(a);
  return b;
}
// CHECK: Verified: two

// A continue tests the condition again, with its call.
int skip(int n)
  cv::pre(0 <= n && n < 100)
  cv::post(cv::result == n)
{
  int k = 0;
  for (int i = 0; inc(i) <= n; i = i + 1)
    cv::invariant(0 <= i && i <= n && k == i)
    cv::decreases(n - i)
  {
    k = k + 1;
    if (k > 0)
      continue;
  }
  return k;
}
// CHECK: Verified: skip

int stepped(int n)
  cv::pre(0 <= n && n < 100)
  cv::post(cv::result == n)
{
  int i = 0;
  for (; i < n; i = inc(i))
    cv::invariant(0 <= i && i <= n)
    cv::decreases(n - i)
  {
  }
  return i;
}
// CHECK: Verified: stepped

// An else-if condition's call runs only on the else path.
int classify(int x)
  cv::pre(-5000 <= x && x <= 5000)
  cv::post(cv::result == (x >= 999 ? 2 : (x + 1 > 5 ? 1 : 0)))
{
  if (x >= 999)
    return 2;
  else if (inc(x) > 5)
    return 1;
  return 0;
}
// CHECK: Verified: classify

int classify_wrong(int x)
  cv::pre(-5000 <= x && x <= 5000)
  cv::post(cv::result != 1 || x > 5)
{
  if (x >= 999)
    return 2;
  else if (inc(x) > 5)
    return 1;
  return 0;
}
// CHECK: error: verification failed: classify_wrong {{.*}}postcondition
// CHECK: note: counterexample: {{.*}}x = 5{{( ->|,|$)}}

int *first_of(int *a)
  cv::pre(cv::valid(a, 2))
  cv::post(cv::result == a)
{
  return a;
}
// CHECK: Verified: first_of

// A pointer result on one path.
int pick(int *a, bool c)
  cv::pre(cv::valid(a, 2))
  cv::post(cv::result == (c ? a[0] : 0))
{
  int *q = c ? first_of(a) : nullptr;
  if (q == nullptr)
    return 0;
  return *q;
}
// CHECK: Verified: pick

// C++17 evaluates the right operand of an assignment before the left one:
// the value is read before the target's call writes *p, and a target that
// reads *p is located after the value's call. Before C++17 the operands are
// unsequenced, and an order that matters is an error.
void target_call(int *a, int *p)
  cv::pre(cv::valid(a, 4) && p != nullptr && 0 <= *p && *p < 2)
  cv::modifies(*p, a[0 : 4])
  cv::post(a[cv::old(*p) + 1] == cv::old(*p))
{
  a[add_one(p)] = *p;
}
// CHECK: Verified: target_call
// CXX14-DAG: error: target_call: before C++17 the order of an assignment's operands is open
// VCR-LABEL: fn target_call
// VCR: assign __value_[[V:[0-9]+]]
// VCR-NEXT: load
// VCR-NEXT: p
// VCR-NEXT: call add_one -> __call_[[A:[0-9]+]]
// VCR: store
// VCR: __call_[[A]]
// VCR: __value_[[V]]

void target_call_compound(int *a, int *p)
  cv::pre(cv::valid(a, 4) && p != nullptr && 0 <= *p && *p < 2)
  cv::pre(a[*p + 1] == 0)
  cv::modifies(*p, a[0 : 4])
  cv::post(a[cv::old(*p) + 1] == cv::old(*p))
{
  a[add_one(p)] += *p;
}
// CHECK: Verified: target_call_compound
// CXX14-DAG: error: target_call_compound: before C++17 the order of an assignment's operands is open

void value_call(int *a, int *p)
  cv::pre(cv::valid(a, 4) && p != nullptr && 0 <= *p && *p < 2)
  cv::modifies(*p, a[0 : 4])
  cv::post(a[cv::old(*p) + 1] == cv::old(*p) + 1)
{
  a[*p] = add_one(p);
}
// CHECK: Verified: value_call
// CXX14-DAG: error: value_call: before C++17 the order of an assignment's operands is open

// Any order gives the same result: the target's call writes only k.
int any_order(int *a, int i)
  cv::pre(cv::valid(a, 4) && 0 <= i && i < 3)
  cv::modifies(a[0 : 4])
  cv::post(a[i + 1] == 7 && cv::result == i + 1)
{
  int k = i;
  a[add_one(&k)] = 7;
  return k;
}
// CHECK: Verified: any_order
// CXX14-DAG: Verified: any_order

// Locating a variable to assign reads nothing, so the call may write it.
int assign_own(int x)
  cv::pre(0 <= x && x < 100)
  cv::post(cv::result == x + 1)
{
  int y = x;
  y = add_one(&y);
  return y;
}
// CHECK: Verified: assign_own
// CXX14-DAG: Verified: assign_own

#ifdef ORDER
int pair(int a, int b)
  cv::post(cv::result == a)
{
  return a;
}

// add_one writes *p, which the other operand reads.
int order_operands(int *p)
  cv::pre(p != nullptr && 0 <= *p && *p < 100)
  cv::modifies(*p)
{
  return add_one(p) + *p;
}
// ORDER-DAG: error: order_operands: C++ leaves the order of these operands open

int order_arguments(int *p)
  cv::pre(p != nullptr && 0 <= *p && *p < 100)
  cv::modifies(*p)
{
  return pair(add_one(p) + 1, *p);
}
// ORDER-DAG: error: order_arguments: C++ leaves the order of these call arguments open

// A member function that is not const may write its object.
int order_member(Counter &c)
  cv::pre(0 <= c.n && c.n < 100)
  cv::modifies(c.n)
{
  return pair(c.bump_get(), c.n);
}
// ORDER-DAG: error: order_member: C++ leaves the order of these call arguments open

int order_index(int *a, int *p)
  cv::pre(cv::valid(a, 4) && p != nullptr && 0 <= *p && *p < 2)
  cv::modifies(*p)
{
  return a[*p + add_one(p)];
}
// ORDER-DAG: error: order_index: C++ leaves the order of these operands open

// The array a subscript reads, beside a call in its index.
struct Buf {
  int *data;
};

int order_base(Buf *b, int *p)
  cv::pre(b != nullptr && cv::valid(b->data, 4))
  cv::pre(p != nullptr && 0 <= *p && *p < 3)
  cv::modifies(*p)
{
  return b->data[add_one(p)];
}
// ORDER-DAG: error: order_base: C++ leaves the order of these operands open

struct Tally {
  int n;

  // Without cppverify::modifies, it may write its object.
  int bump()
    cv::pre(n < 1000)
  {
    n = n + 1;
    return n;
  }
};

int order_default_member(Tally &t)
  cv::pre(0 <= t.n && t.n < 100)
  cv::modifies(t.n)
{
  return pair(t.bump(), t.n);
}
// ORDER-DAG: error: order_default_member: C++ leaves the order of these call arguments open
#endif
