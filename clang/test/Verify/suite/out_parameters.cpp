// RUN: not %cpp-verify --jobs=1 %s -- -Wno-tautological-compare > %t 2>&1
// RUN: FileCheck %s < %t
// RUN: FileCheck %s --check-prefix=SOUND < %t
// RUN: %cpp-verify --lower-only --dump-ir=1 %s -- -Wno-tautological-compare 2>&1 | FileCheck %s --check-prefix=VCR
// RUN: not %cpp-verify --jobs=1 --no-check-ub %s -- -Wno-tautological-compare 2>&1 | FileCheck %s --check-prefix=NOUB
// RUN: %cpp-verify --lower-only --dump-ir=2 %s -- -Wno-tautological-compare 2>&1 | FileCheck %s --check-prefix=PASSIVE

// Binding a reference or passing a pointer reads nothing ([dcl.init.ref],
// [conv.lval]); only reading an indeterminate value is undefined
// ([basic.indet]). A parameter whose storage the body never reads before
// writing it is an out-parameter: callers may pass storage that is not
// initialized, the body's reads of it are checked against what it wrote,
// and the leaves it writes on every path are initialized when it returns.
// A parameter the body may read first keeps the rule that its storage is
// initialized, and a call that cannot show that is unsupported.
//
// No proof here holds only because no execution reaches its end.
// SOUND-NOT: vacuous

namespace cv = cppverify;

struct Pair {
  int a;
  int b;
};

void init_ref(int &r)
  cv::modifies(r)
  cv::post(r == 0)
{
  r = 0;
}
// CHECK: Verified: init_ref
// NOUB: Verified: init_ref
// VCR-LABEL: fn init_ref
// VCR-NEXT: param r out
// VCR-NEXT: pre
// VCR-NEXT: &&
// VCR-NEXT: !
// VCR-NEXT: ==
// VCR-NEXT: r
// VCR-NEXT: 0
// VCR-NEXT: valid_ptr
// VCR-NEXT: r
// VCR-NEXT: post
// VCR-NEXT: ==
// VCR-NEXT: load
// VCR-NEXT: r
// VCR-NEXT: 0
// VCR-NEXT: initialized_ptr
// VCR-NEXT: r
// VCR-NEXT: modifies

void init_ptr(int *p)
  cv::pre(p != nullptr)
  cv::modifies(*p)
  cv::post(*p == 0)
{
  *p = 0;
}
// CHECK: Verified: init_ptr
// VCR-LABEL: fn init_ptr
// VCR-NEXT: param p out

int read_ref(const int &r)
  cv::post(cv::result == r)
{
  return r;
}
// CHECK: Verified: read_ref
// VCR-LABEL: fn read_ref
// VCR-NEXT: param r{{$}}
// VCR: initialized_ptr

int scalar_out()
  cv::post(cv::result == 0)
{
  int a;
  init_ref(a);
  return a;
}
// CHECK: Verified: scalar_out

int array_out()
  cv::post(cv::result == 0)
{
  int a[2];
  init_ref(a[0]);
  return a[0];
}
// CHECK: Verified: array_out
// NOUB: Verified: array_out

int heap_out()
  cv::post(cv::result == 0)
{
  int *p = new int;
  init_ptr(p);
  int v = *p;
  delete p;
  return v;
}
// CHECK: Verified: heap_out
// NOUB: Verified: heap_out

int initialized_argument()
  cv::post(cv::result == 0)
{
  int a = 7;
  init_ref(a);
  return a;
}
// CHECK: Verified: initialized_argument

int written_through_local_reference()
  cv::post(cv::result == 3)
{
  int a;
  int &r = a;
  r = 3;
  return a;
}
// CHECK: Verified: written_through_local_reference

int read_before_written()
  cv::post(cv::result == 3)
{
  int a;
  int &r = a;
  int v = r;
  return v;
}
// CHECK: :[[@LINE-3]]:3: error: verification failed: read_before_written [initialization]

int *fresh()
  cv::post(cv::result != nullptr)
{
  int *p = new int;
  return p;
}
// CHECK: Unresolved: fresh {{.*}}[reason=construct.unsupported] (the verifier cannot model a construct here: returning a pointer to storage that is not initialized, since callers read a returned pointer's storage as initialized)

// The callee reads the indeterminate value, which is undefined, but its
// verification cannot say that it reads before it writes: unsupported.
int reads_uninitialized()
  cv::post(cv::result == 0)
{
  int a;
  return read_ref(a);
}
// CHECK: Unresolved: reads_uninitialized {{.*}}[reason=construct.unsupported] (the verifier cannot model a construct here: binding a reference or pointer parameter to storage that is not initialized, which the callee may read before writing it)

// Written on every path, with no postcondition about it: initialized after
// the call, its value unknown.
void set_some(int &x)
  cv::modifies(x)
{
  x = 1;
}
// CHECK: Verified: set_some
// VCR-LABEL: fn set_some
// VCR-NEXT: param x out
// VCR: post
// VCR-NEXT: initialized_ptr
// VCR-NEXT: x
// VCR-NEXT: modifies

int reads_what_was_set()
  cv::post(cv::result == 0)
{
  int a[1];
  set_some(a[0]);
  int v = a[0];
  return 0;
}
// CHECK: Verified: reads_what_was_set
// NOUB: Verified: reads_what_was_set

// Written on one path: the postcondition says on which.
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
// VCR-LABEL: fn try_get
// VCR-NEXT: param out out
// VCR-NEXT: param ok
// VCR: post
// VCR-NOT: initialized_ptr
// VCR: modifies

int got(bool ok)
  cv::post(cv::result == 5 || cv::result == 0)
{
  int a[1];
  bool found = try_get(a[0], ok);
  if (found)
    return a[0];
  return 0;
}
// CHECK: Verified: got
// NOUB: Verified: got

int reads_after_failed_get()
  cv::post(cv::result == 0)
{
  int a[1];
  try_get(a[0], false);
  return a[0];
}
// CHECK: :[[@LINE-2]]:3: error: verification failed: reads_after_failed_get [initialization]
// NOUB: :[[@LINE-3]]:3: error: verification failed: reads_after_failed_get [initialization]

// Written, then read: still an out-parameter.
void write_then_update(int &x)
  cv::modifies(x)
  cv::post(x == 1)
{
  x = 0;
  x = x + 1;
}
// CHECK: Verified: write_then_update
// VCR-LABEL: fn write_then_update
// VCR-NEXT: param x out

int updated()
  cv::post(cv::result == 1)
{
  int a[1];
  write_then_update(a[0]);
  return a[0];
}
// CHECK: Verified: updated

// Read on a path before it is written: an input.
void reset_or_bump(int &x, bool c)
  cv::pre(c || x < 100)
  cv::modifies(x)
  cv::post(x <= 100)
{
  if (c)
    x = 0;
  x = x + 1;
}
// CHECK: Verified: reset_or_bump
// VCR-LABEL: fn reset_or_bump
// VCR-NEXT: param x{{$}}

int reset_uninitialized()
  cv::post(cv::result == 1)
{
  int a[1];
  reset_or_bump(a[0], true);
  return a[0];
}
// CHECK: Unresolved: reset_uninitialized {{.*}}[reason=construct.unsupported]

// The contract reads the entry value: an input.
void clamp_nonnegative(int &x)
  cv::pre(x >= -5)
  cv::modifies(x)
  cv::post(x >= 0)
{
  x = 0;
}
// CHECK: Verified: clamp_nonnegative
// VCR-LABEL: fn clamp_nonnegative
// VCR-NEXT: param x{{$}}

void zero_if(int &x, bool c)
  cv::modifies(x)
  cv::post(c ? x == 0 : x == cv::old(x))
{
  if (c)
    x = 0;
}
// CHECK: Verified: zero_if
// VCR-LABEL: fn zero_if
// VCR-NEXT: param x{{$}}

// Passed on: what the callee writes on every path is written here.
void set_twice(int &r)
  cv::modifies(r)
  cv::post(r == 2)
{
  set_some(r);
  int seen = r;
  r = 2;
}
// CHECK: Verified: set_twice
// VCR-LABEL: fn set_twice
// VCR-NEXT: param r out

int set_through()
  cv::post(cv::result == 2)
{
  int a[1];
  set_twice(a[0]);
  return a[0];
}
// CHECK: Verified: set_through

// Written, then passed to a callee that reads it; read by a callee first.
void write_then_read(int &x)
  cv::modifies(x)
  cv::post(x == 4)
{
  x = 4;
  int v = read_ref(x);
}
// CHECK: Verified: write_then_read
// VCR-LABEL: fn write_then_read
// VCR-NEXT: param x out

void read_then_write(int &x)
  cv::modifies(x)
  cv::post(x == 4)
{
  int v = read_ref(x);
  x = 4;
}
// CHECK: Verified: read_then_write
// VCR-LABEL: fn read_then_write
// VCR-NEXT: param x{{$}}

[[cppverify::trusted]] void external_set(int &x)
  cv::modifies(x)
  cv::post(x == 1);
// CHECK: Trusted: external_set

// A callee without a verified body may read what it receives: an input.
void through_external(int &x)
  cv::modifies(x)
  cv::post(x == 1)
{
  external_set(x);
}
// CHECK: Verified: through_external
// VCR-LABEL: fn through_external
// VCR-NEXT: param x{{$}}

// A record written field by field.
void make_pair(Pair &p)
  cv::modifies(p)
  cv::post(p.a == 1)
{
  p.a = 1;
  p.b = 2;
}
// CHECK: Verified: make_pair
// NOUB: Verified: make_pair
// VCR-LABEL: fn make_pair
// VCR-NEXT: param p out
// VCR: post
// VCR: initialized_ptr
// VCR-NEXT: p
// VCR-NEXT: initialized_ptr
// VCR-NEXT: +
// VCR-NEXT: p
// VCR-NEXT: 4

int made()
  cv::post(cv::result == 1)
{
  Pair p;
  make_pair(p);
  int b = p.b;
  return p.a;
}
// CHECK: Verified: made

// Its fields bound to a callee's out-parameter, one after the other.
void make_by_parts(Pair &p)
  cv::modifies(p)
  cv::post(p.a == 0 && p.b == 0)
{
  init_ref(p.a);
  init_ref(p.b);
}
// CHECK: Verified: make_by_parts
// VCR-LABEL: fn make_by_parts
// VCR-NEXT: param p out

int made_by_parts()
  cv::post(cv::result == 0)
{
  Pair p;
  make_by_parts(p);
  return p.a + p.b;
}
// CHECK: Verified: made_by_parts

// One field written, then the record passed to a callee that reads both:
// an input.
int second_of(const Pair &q)
  cv::post(cv::result == q.b)
{
  return q.b;
}
// CHECK: Verified: second_of

void write_a_then_read(Pair &p)
  cv::modifies(p)
  cv::post(p.a == 1 && p.b == 2)
{
  p.a = 1;
  int b = second_of(p);
  p.b = 2;
}
// CHECK: Verified: write_a_then_read
// VCR-LABEL: fn write_a_then_read
// VCR-NEXT: param p{{$}}

void make_first(Pair &p)
  cv::modifies(p)
  cv::post(p.a == 1)
{
  p.a = 1;
}
// CHECK: Verified: make_first

int reads_unmade()
  cv::post(cv::result == 1)
{
  Pair p;
  make_first(p);
  return p.b;
}
// CHECK: :[[@LINE-2]]:3: error: verification failed: reads_unmade [initialization]

// A postcondition about storage the function never writes speaks of the
// caller's values: an input, initialized at entry.
void untouched(int &x)
  cv::modifies(x)
  cv::post(x == x)
{
}
// CHECK: Verified: untouched
// VCR-LABEL: fn untouched
// VCR-NEXT: param x{{$}}

// One that it writes on a path: a read of what it wrote.
void set_if(int &x, bool c)
  cv::modifies(x)
  cv::post(x == 1)
{
  if (c)
    x = 1;
}
// CHECK: :[[@LINE-5]]:14: error: verification failed: set_if [initialization]
// NOUB: :[[@LINE-6]]:14: error: verification failed: set_if [initialization]

// A loop writes on no path known before it runs.
void zero_each(int &x, int n)
  cv::pre(n >= 0)
  cv::modifies(x)
{
  for (int i = 0; i < n; i = i + 1)
    cv::invariant(0 <= i && i <= n)
    cv::decreases(n - i)
  {
    x = 0;
  }
}
// CHECK: Verified: zero_each
// VCR-LABEL: fn zero_each
// VCR-NEXT: param x out
// VCR-NEXT: param n
// VCR: post
// VCR-NEXT: modifies

int maybe_zeroed()
  cv::post(cv::result == 0)
{
  int a[1];
  zero_each(a[0], 0);
  return a[0];
}
// CHECK: :[[@LINE-2]]:3: error: verification failed: maybe_zeroed [initialization]

// A call that may write a cell keeps it initialized.
int kept_through_call(int n)
  cv::pre(n >= 0)
{
  int a[1];
  a[0] = 7;
  zero_each(a[0], n);
  return a[0];
}
// CHECK: Verified: kept_through_call

// One that writes nothing changes no initialization.
void leave(int &x)
  cv::post(true)
{
}
// CHECK: Verified: leave

int kept_by_leave()
  cv::post(cv::result == 3)
{
  int a[1];
  a[0] = 3;
  leave(a[0]);
  return a[0];
}
// CHECK: Verified: kept_by_leave

// So does a loop that writes it.
void count_up_into(int &out, int n)
  cv::pre(0 <= n && n < 100)
  cv::modifies(out)
  cv::post(out == n)
{
  out = 0;
  for (int i = 0; i < n; i = i + 1)
    cv::invariant(0 <= i && i <= n && out == i)
    cv::decreases(n - i)
  {
    out = out + 1;
  }
}
// CHECK: Verified: count_up_into
// VCR-LABEL: fn count_up_into
// VCR-NEXT: param out out
// Only the cell the loop writes may become initialized at its head.
// PASSIVE-LABEL: passive count_up_into
// PASSIVE: heap_store __heap_init_1 -> __heap_init_2
// PASSIVE-NEXT: out_0
// PASSIVE-NEXT: ||
// PASSIVE-NEXT: load
// PASSIVE-NEXT: out_0
// PASSIVE-NEXT: __loop_initialized_1

// Calls in a loop: each keeps what was initialized before it.
int init_in_loop()
  cv::post(cv::result == 0)
{
  int a[1];
  init_ref(a[0]);
  for (int i = 0; i < 3; i = i + 1)
    cv::invariant(0 <= i && i <= 3 && a[0] == 0)
    cv::decreases(3 - i)
  {
    init_ref(a[0]);
  }
  return a[0];
}
// CHECK: Verified: init_in_loop

// What a call in one iteration initializes, the next reads.
int init_once_in_loop()
  cv::post(cv::result == 0)
{
  int a[1];
  int s = 0;
  for (int i = 0; i < 3; i = i + 1)
    cv::invariant(0 <= i && i <= 3 && s == 0)
    cv::invariant(i == 0 || a[0] == 0)
    cv::decreases(3 - i)
  {
    if (i == 0)
      init_ref(a[0]);
    s = s + a[0];
  }
  return s;
}
// CHECK: Verified: init_once_in_loop

int init_in_loop_only(int n)
  cv::pre(0 <= n && n <= 3)
  cv::post(cv::result == 0)
{
  int a[1];
  for (int i = 0; i < n; i = i + 1)
    cv::invariant(0 <= i && i <= n)
    cv::decreases(n - i)
  {
    init_ref(a[0]);
  }
  return a[0];
}
// CHECK: :[[@LINE-2]]:3: error: verification failed: init_in_loop_only [initialization]

void zero_rec(int &x, int n)
  cv::pre(n >= 0)
  cv::modifies(x)
  cv::post(x == 0)
  cv::decreases(n)
{
  if (n == 0) {
    x = 0;
    return;
  }
  zero_rec(x, n - 1);
}
// CHECK: Verified: zero_rec
// VCR-LABEL: fn zero_rec
// VCR-NEXT: param x out

// A null test reads nothing.
void set_if_given(int *p)
  cv::modifies(*p)
  cv::post(p == nullptr || *p == 7)
{
  if (p)
    *p = 7;
}
// CHECK: Verified: set_if_given
// VCR-LABEL: fn set_if_given
// VCR-NEXT: param p out

int given()
  cv::post(cv::result == 7)
{
  int *p = new int;
  set_if_given(p);
  int v = *p;
  delete p;
  return v;
}
// CHECK: Verified: given

// A copy of the pointer is a use of it: an input.
void through_copy(int *p)
  cv::pre(p != nullptr)
  cv::modifies(*p)
  cv::post(*p == 3)
{
  int *q = p;
  *q = 3;
}
// CHECK: Verified: through_copy
// VCR-LABEL: fn through_copy
// VCR-NEXT: param p{{$}}

// Through a copy of the pointer, a read is not seen as one: an input, so a
// caller cannot pass a record that is not initialized.
void through_alias(Pair *p)
  cv::pre(p != nullptr)
  cv::modifies(*p)
  cv::post(p->a == 1)
{
  Pair *q = p;
  int seen = q->b;
  p->a = 1;
  p->b = 2;
}
// CHECK: Verified: through_alias
// VCR-LABEL: fn through_alias
// VCR-NEXT: param p{{$}}

int alias_reads_garbage()
  cv::post(cv::result == 1)
{
  Pair x;
  through_alias(&x);
  return x.a;
}
// CHECK: Unresolved: alias_reads_garbage {{.*}}[reason=construct.unsupported]

// A loop that fills an array, and a function that passes its array on.
void fill(int *p, int n)
  cv::pre(n >= 0 && cv::valid(p, n))
  cv::modifies(p[0 : n])
  cv::post(cv::forall(k, 0, n, p[k] == 0))
{
  for (int i = 0; i < n; i = i + 1)
    cv::invariant(0 <= i && i <= n)
    cv::invariant(cv::forall(k, 0, i, p[k] == 0))
    cv::decreases(n - i)
  {
    p[i] = 0;
  }
}
// CHECK: Verified: fill
// VCR-LABEL: fn fill
// VCR-NEXT: param p out

void fill_four(int *b)
  cv::pre(cv::valid(b, 4))
  cv::modifies(b[0 : 4])
  cv::post(cv::forall(k, 0, 4, b[k] == 0))
{
  fill(b, 4);
}
// CHECK: Verified: fill_four

void fill_three(int *b)
  cv::pre(cv::valid(b, 4))
  cv::modifies(b[0 : 4])
  cv::post(cv::forall(k, 0, 4, b[k] == 0))
{
  fill(b, 3);
}
// CHECK: :[[@LINE-4]]:12: error: verification failed: fill_three [initialization]

// A member function that writes its object.
struct Point {
  int x;
  int y;
  void reset()
    cv::modifies(*this)
  {
    x = 0;
    y = 0;
  }
};
// CHECK: Verified: Point::reset
// NOUB: Verified: Point::reset
// VCR-LABEL: fn Point::reset
// VCR-NEXT: param this out

int reset_point()
  cv::post(cv::result == 0)
{
  Point p;
  p.reset();
  int y = p.y;
  return 0;
}
// CHECK: Verified: reset_point

