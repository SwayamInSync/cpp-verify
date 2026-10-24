// RUN: not %cpp-verify --jobs=1 %s -- 2>&1 | FileCheck %s
// RUN: %cpp-verify --lower-only --dump-ir=1 %s -- -DLOWER 2>&1 \
// RUN:   | FileCheck %s --check-prefix=VCR
// RUN: not %cpp-verify --jobs=1 --backend=bmc --unroll=1 %s -- 2>&1 \
// RUN:   | FileCheck %s --check-prefix=BMC
//
// A reference to a record is a pointer to it that is never null and never
// reseated: its fields and elements are places in the object it names, as
// p->f is for a pointer, and modifies(c) is that object, as modifies(*p) is.

struct Counter {
  int n;
  int limit;
};

struct Pair {
  Counter left;
  Counter right;
};

struct Ring {
  int buf[4];
  int head;
};

void reset(Counter &c)
  cppverify::modifies(c)
  cppverify::post(c.n == 0 && c.limit == 10)
{
  c.n = 0;
  c.limit = 10;
}
// CHECK-DAG: Verified: reset [backend=z3]
// BMC-DAG: Verified: reset [backend=bmc, bound=0]
// VCR-LABEL: fn reset
// VCR:      modifies
// VCR-NEXT:   load
// VCR-NEXT:     c
// VCR-NEXT: body

// A record inside an object, through a reference or a pointer, is its bytes.
void left_only(Pair &p)
  cppverify::modifies(p.left)
  cppverify::post(p.left.n == 0 && p.right.n == cppverify::old(p.right.n))
{
  reset(p.left);
}
// CHECK-DAG: Verified: left_only [backend=z3]
// VCR-LABEL: fn left_only
// VCR:      modifies
// VCR-NEXT:   load
// VCR-NEXT:     +
// VCR-NEXT:       p
// VCR-NEXT:       0
// VCR-NEXT:   range 8
// VCR-NEXT:     1
// VCR-NEXT: body

void right_only(Pair *p)
  cppverify::pre(p != nullptr)
  cppverify::modifies(p->right)
  cppverify::post(p->right.limit == 10 && p->left.n == cppverify::old(p->left.n))
{
  reset(p->right);
}
// CHECK-DAG: Verified: right_only [backend=z3]

#ifndef LOWER
void bump(Counter &c)
  cppverify::pre(c.n < c.limit)
  cppverify::modifies(c.n)
  cppverify::post(c.n == cppverify::old(c.n) + 1)
  cppverify::post(c.limit == cppverify::old(c.limit))
{
  c.n = c.n + 1;
}
// CHECK-DAG: Verified: bump [backend=z3]
// BMC-DAG: Verified: bump [backend=bmc, bound=0]

int read(const Counter &c)
  cppverify::post(cppverify::result == c.n)
{
  return c.n;
}
// CHECK-DAG: Verified: read [backend=z3]

// A reference passed on, from a reference, a pointer, and a field.
void twice(Counter &c)
  cppverify::pre(c.n + 1 < c.limit)
  cppverify::modifies(c.n)
  cppverify::post(c.n == cppverify::old(c.n) + 2)
{
  bump(c);
  bump(c);
}
// CHECK-DAG: Verified: twice [backend=z3]

void via_pointer(Counter *p)
  cppverify::pre(p != nullptr && p->n < p->limit)
  cppverify::modifies(p->n)
  cppverify::post(p->n == cppverify::old(p->n) + 1)
{
  bump(*p);
}
// CHECK-DAG: Verified: via_pointer [backend=z3]

void via_field(Pair &p)
  cppverify::pre(p.left.n < p.left.limit)
  cppverify::modifies(p.left.n)
  cppverify::post(p.left.n == cppverify::old(p.left.n) + 1)
  cppverify::post(p.right.n == cppverify::old(p.right.n))
{
  bump(p.left);
}
// CHECK-DAG: Verified: via_field [backend=z3]

// Two mutable references name distinct objects unless aliases says so.
void frame(Counter &a, Counter &b)
  cppverify::modifies(a)
  cppverify::post(a.n == 0 && b.n == cppverify::old(b.n))
{
  reset(a);
}
// CHECK-DAG: Verified: frame [backend=z3]

void self_frame(Counter &c)
  cppverify::modifies(c)
{
  frame(c, c);
}
// CHECK-DAG: error: verification failed: self_frame [{{.*}}::aliasing@[[@LINE-2]]:3] (counterexample: c [ssa=c_0] [type=pointer] =

void may_alias(Counter &a, Counter &b)
  cppverify::aliases(a, b)
  cppverify::modifies(a.n)
  cppverify::post(b.n == 5)
{
  a.n = 5;
}
// CHECK-DAG: error: verification failed: may_alias [{{.*}}::postcondition@[[@LINE-4]]:23]

int sum(const Counter &a, const Counter &b)
  cppverify::pre(-1000 < a.n && a.n < 1000 && -1000 < b.n && b.n < 1000)
  cppverify::post(cppverify::result == a.n + b.n)
{
  return a.n + b.n;
}

int sum_same(Counter &c)
  cppverify::pre(-1000 < c.n && c.n < 1000)
  cppverify::post(cppverify::result == 2 * c.n)
{
  return sum(c, c);
}
// CHECK-DAG: Verified: sum_same [backend=z3]

// Each store lies in a footprint, and a callee's footprints in the caller's.
void bad_frame(Counter &c)
  cppverify::modifies(c.n)
{
  c.limit = 3;
}
// CHECK-DAG: error: verification failed: bad_frame [{{.*}}::frame@[[@LINE-2]]:11]

void narrow_caller(Counter &c)
  cppverify::modifies(c.n)
{
  reset(c);
}
// CHECK-DAG: error: verification failed: narrow_caller [{{.*}}::frame@[[@LINE-2]]:3]

void narrow_member(Pair &p)
  cppverify::modifies(p.left.n)
{
  reset(p.left);
}
// CHECK-DAG: error: verification failed: narrow_member [{{.*}}::frame@[[@LINE-2]]:3]

// A callee's whole record is every byte of it, which only a footprint naming
// the record, or an object around it, contains; its fields one by one do not.
void fields_one_by_one(Pair &p)
  cppverify::modifies(p.left.n, p.left.limit)
{
  reset(p.left);
}
// CHECK-DAG: error: verification failed: fields_one_by_one [{{.*}}::frame@[[@LINE-2]]:3]

// Array members: indices bounded by their array, and pointers into them
// bounded by it.
void put(Ring &r, int v)
  cppverify::pre(0 <= r.head && r.head < 4)
  cppverify::modifies(r.buf[r.head])
  cppverify::post(r.buf[r.head] == v && r.head == cppverify::old(r.head))
{
  r.buf[r.head] = v;
}
// CHECK-DAG: Verified: put [backend=z3]

void put_at(Ring &r, int i, int v)
  cppverify::pre(0 <= i && i <= 4)
  cppverify::modifies(r.buf[0 : 4])
{
  r.buf[i] = v;
}
// CHECK-DAG: error: verification failed: put_at [{{.*}}::bounds@[[@LINE-2]]:12]

void set_first(int *q, int v)
  cppverify::pre(cppverify::valid(q, 4))
  cppverify::modifies(q[0])
  cppverify::post(q[0] == v)
{
  q[0] = v;
}

void set_through_decay(Ring &r)
  cppverify::modifies(r.buf[0])
  cppverify::post(r.buf[0] == 7 && r.head == cppverify::old(r.head))
{
  set_first(r.buf, 7);
}
// CHECK-DAG: Verified: set_through_decay [backend=z3]

int head_through_pointer(const Ring &r)
  cppverify::post(cppverify::result == r.head)
{
  const int *h = &r.head;
  return *h;
}
// CHECK-DAG: Verified: head_through_pointer [backend=z3]

int read_object(const Counter *p)
  cppverify::pre(p != nullptr)
  cppverify::post(cppverify::result == p->n)
{
  return p->n;
}

int through_address(const Counter &c)
  cppverify::post(cppverify::result == c.n)
{
  return read_object(&c);
}
// CHECK-DAG: Verified: through_address [backend=z3]

int past_head(const Ring &r)
{
  const int *h = &r.head;
  cppverify::check(h[1] == 0);
  return 0;
}
// CHECK-DAG: error: verification failed: past_head [{{.*}}::bounds@[[@LINE-3]]:3]

// Local references to records bind a place as a parameter does.
void local_deref(Counter *p)
  cppverify::pre(p != nullptr)
  cppverify::modifies(*p)
  cppverify::post(p->n == 0)
{
  Counter &r = *p;
  r.n = 0;
}
// CHECK-DAG: Verified: local_deref [backend=z3]

void local_member(Pair *p)
  cppverify::pre(p != nullptr && p->left.n < p->left.limit)
  cppverify::modifies(p->left.n)
  cppverify::post(p->left.n == cppverify::old(p->left.n) + 1)
{
  Counter &r = p->left;
  Counter &s = r;
  bump(s);
}
// CHECK-DAG: Verified: local_member [backend=z3]

void local_wrong_member(Pair *p)
  cppverify::pre(p != nullptr)
  cppverify::modifies(p->left)
{
  Counter &r = p->right;
  r.n = 0;
}
// CHECK-DAG: error: verification failed: local_wrong_member [{{.*}}::frame@[[@LINE-2]]:7]

void local_elements(Counter *a, int n)
  cppverify::pre(cppverify::valid(a, n) && n >= 0)
  cppverify::modifies(a[0 : n])
  cppverify::post(cppverify::forall(k, 0, n, a[k].n == 0))
{
  for (int i = 0; i < n; i = i + 1)
    cppverify::invariant(0 <= i && i <= n)
    cppverify::invariant(cppverify::forall(k, 0, i, a[k].n == 0))
    cppverify::decreases(n - i)
  {
    Counter &r = a[i];
    r.n = 0;
  }
}
// CHECK-DAG: Verified: local_elements [backend=z3]

void local_past(Counter *a, int i)
  cppverify::pre(cppverify::valid(a, 4) && 0 <= i && i <= 4)
  cppverify::modifies(a[0 : 4])
{
  Counter &r = a[i];
  r.n = 3;
}
// CHECK-DAG: error: verification failed: local_past [{{.*}}::dereference@[[@LINE-3]]:3] (counterexample: a [ssa=a_0] [type=pointer] = {{[0-9]+}}, i [ssa=i_0] [type=i32] = 4)

// A local record bound to a reference is one object in memory.
int local_object()
  cppverify::post(cppverify::result == 1)
{
  Counter c;
  c.n = 0;
  Counter &r = c;
  r.n = 1;
  return c.n;
}
// CHECK-DAG: Verified: local_object [backend=z3]

int local_object_uninitialized()
  cppverify::post(cppverify::result == 0)
{
  Counter c;
  c.n = 0;
  Counter &r = c;
  return r.limit;
}
// CHECK-DAG: error: verification failed: local_object_uninitialized [{{.*}}::initialization@[[@LINE-2]]:3]

// A type invariant is a fact about records by value; one a reference names is
// an object whose fields the function reads from memory.
struct Bounded {
  int v;
  cppverify::type_invariant(v >= 0);
};

int by_value(Bounded b)
  cppverify::post(cppverify::result >= 0)
{
  return b.v;
}
// CHECK-DAG: Verified: by_value [backend=z3]

int by_reference(const Bounded &b)
  cppverify::post(cppverify::result >= 0)
{
  return b.v;
}
// CHECK-DAG: error: verification failed: by_reference [{{.*}}::postcondition@[[@LINE-4]]:37]

// A local passed to a callee by reference is checked at the call (see
// local_record_arguments.cpp). Not yet: a pointer formed from a local through
// a reference, a whole record read through one, a proof function's
// reference, and rvalue and volatile references.
int local_to_callee()
  cppverify::post(cppverify::result == 1)
{
  Counter c;
  c.n = 0;
  c.limit = 5;
  bump(c);
  return c.n;
}
// CHECK-DAG: Verified: local_to_callee [backend=z3]

int local_address()
  cppverify::post(cppverify::result == 0)
{
  Ring local;
  Ring &r = local;
  int *q = &r.head;
  return 0;
}
// CHECK-DAG: error: local_address: raw address-of is unsupported until lexical lifetime and escape effects are modeled

int local_decay()
  cppverify::post(cppverify::result == 0)
{
  Ring local;
  local.buf[0] = 1;
  Ring &r = local;
  int *q = r.buf;
  return 0;
}
// CHECK-DAG: error: local_decay: array-to-pointer decay of automatic storage is unsupported until lexical lifetime and escape effects are modeled

int by_copy(Counter c)
  cppverify::post(cppverify::result == c.n)
{
  return c.n;
}

int whole_read(const Pair &p)
  cppverify::post(cppverify::result == p.left.n)
{
  return by_copy(p.left);
}
// CHECK-DAG: error: whole_read: a record or array read as a whole through a pointer or reference is unsupported; read its fields

cppverify::proof void proof_reference(Counter &c)
  cppverify::post(true)
{
}
// CHECK-DAG: error: proof_reference: unsupported C++ type in verification: Counter &

int rvalue_reference(Counter &&c)
  cppverify::post(cppverify::result == c.n)
{
  return c.n;
}
// CHECK-DAG: error: rvalue_reference: unsupported C++ type in verification: Counter &&

int volatile_reference(volatile Counter &c)
  cppverify::post(cppverify::result == c.n)
{
  return c.n;
}
// CHECK-DAG: error: volatile_reference: unsupported C++ type in verification: volatile Counter &
#endif
