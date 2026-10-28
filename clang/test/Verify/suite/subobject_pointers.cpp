// RUN: not %cpp-verify --jobs=1 %s -- 2>&1 | FileCheck %s
// RUN: %cpp-verify --lower-only --no-check-ub --dump-ir=1 %s -- 2>&1 \
// RUN:   | FileCheck %s --check-prefix=VCR
// RUN: not %cpp-verify --jobs=1 %s -- -DESCAPE 2>&1 \
// RUN:   | FileCheck %s --check-prefix=ESCAPE
//
// A pointer to a subobject of the object a pointer addresses (a member array
// it decays from, an element of one, a field, a nested record) addresses only
// that subobject's bytes: the array, or the field or record. Every access and
// step through it, and every argument formed from it, stays there, as CHERI's
// subobject bounds do in hardware. The address of a byte one past an array is
// the next field, inside the object, and is still out of bounds.

struct Inner {
  int x;
  int y;
  int arr[3];
};

struct Item {
  int v;
  int w;
};

struct Ring {
  int buf[8];
  int head;
  Inner inner;
  int grid[3][4];
  Item items[4];
  int other[2];
};

#ifndef ESCAPE
int first(const int *p, int n)
  cppverify::pre(cppverify::valid(p, n) && n >= 1)
  cppverify::post(cppverify::result == p[0])
{
  return p[0];
}
// CHECK-DAG: Verified: first [backend=z3]

int get(const int *p)
  cppverify::pre(p != nullptr)
  cppverify::post(cppverify::result == *p)
{
  return *p;
}
// CHECK-DAG: Verified: get [backend=z3]

void set(int *p, int v)
  cppverify::pre(p != nullptr)
  cppverify::modifies(*p)
  cppverify::post(*p == v)
{
  *p = v;
}
// CHECK-DAG: Verified: set [backend=z3]

int inner_x(const Inner *p)
  cppverify::pre(p != nullptr)
  cppverify::post(cppverify::result == p->x)
{
  return p->x;
}
// CHECK-DAG: Verified: inner_x [backend=z3]

// The member array passed as a buffer, whole and from an element on.
int pass_member(const Ring *r)
  cppverify::pre(r != nullptr)
  cppverify::post(cppverify::result == r->buf[0])
{
  return first(r->buf, 8);
}
// CHECK-DAG: Verified: pass_member [backend=z3]
// VCR-LABEL: fn pass_member
// VCR:      assign __subobject_1
// VCR-NEXT:   +
// VCR-NEXT:     r
// VCR-NEXT:     0
// VCR-NEXT: assign __subobject_1.__lo
// VCR-NEXT:   +
// VCR-NEXT:     r
// VCR-NEXT:     0
// VCR-NEXT: assign __subobject_1.__hi
// VCR-NEXT:   +
// VCR-NEXT:     +
// VCR-NEXT:       r
// VCR-NEXT:       0
// VCR-NEXT:     32
// VCR-NEXT: call first
// VCR-NEXT:   __subobject_1

int pass_tail(const Ring *r)
  cppverify::pre(r != nullptr)
  cppverify::post(cppverify::result == r->buf[5])
{
  return first(r->buf + 5, 3);
}
// CHECK-DAG: Verified: pass_tail [backend=z3]

// A local pointer keeps the bounds of the array it comes from.
int local_walk(const Ring *r)
  cppverify::pre(r != nullptr)
  cppverify::post(cppverify::result == r->buf[7])
{
  const int *q = r->buf;
  return q[7];
}
// CHECK-DAG: Verified: local_walk [backend=z3]
// VCR-LABEL: fn local_walk
// VCR:      assign q.__lo
// VCR-NEXT:   0
// VCR-NEXT: assign q.__hi
// VCR-NEXT:   18446744073709551616
// VCR:      assign q.__lo
// VCR-NEXT:   __subobject_{{[0-9]+}}.__lo
// VCR-NEXT: assign q.__hi
// VCR-NEXT:   __subobject_{{[0-9]+}}.__hi
// VCR-NEXT: assign q
// VCR-NEXT:   __subobject_{{[0-9]+}}

int element_address(const Ring *r)
  cppverify::pre(r != nullptr)
  cppverify::post(cppverify::result == r->buf[0])
{
  const int *q = &r->buf[2];
  return q[-2];
}
// CHECK-DAG: Verified: element_address [backend=z3]

void field_address(Ring *r)
  cppverify::pre(r != nullptr)
  cppverify::modifies(r->head)
  cppverify::post(r->head == 5)
{
  set(&r->head, 5);
}
// CHECK-DAG: Verified: field_address [backend=z3]

int record_address(const Ring *r)
  cppverify::pre(r != nullptr)
  cppverify::post(cppverify::result == r->inner.x)
{
  return inner_x(&r->inner);
}
// CHECK-DAG: Verified: record_address [backend=z3]

int nested_member(const Ring *r)
  cppverify::pre(r != nullptr)
  cppverify::post(cppverify::result == r->inner.arr[2])
{
  const Inner *in = &r->inner;
  return in->arr[2];
}
// CHECK-DAG: Verified: nested_member [backend=z3]

int row(const Ring *r, int i)
  cppverify::pre(r != nullptr && 0 <= i && i < 3)
  cppverify::post(cppverify::result == r->grid[i][3])
{
  const int *q = r->grid[i];
  return q[3];
}
// CHECK-DAG: Verified: row [backend=z3]

int item_field(const Ring *r, int k)
  cppverify::pre(r != nullptr && 0 <= k && k < 4)
  cppverify::post(cppverify::result == r->items[k].w)
{
  const Item *it = &r->items[k];
  return it->w;
}
// CHECK-DAG: Verified: item_field [backend=z3]

// The address of an element of a parameter's own buffer.
int param_element(const int *a, int n)
  cppverify::pre(cppverify::valid(a, n) && n >= 4)
  cppverify::post(cppverify::result == a[2])
{
  return get(&a[2]);
}
// CHECK-DAG: Verified: param_element [backend=z3]

// A pointer stepped through the member, compared with its end, and measured
// by a pointer difference.
int sum8(const Ring *r)
  cppverify::pre(r != nullptr)
  cppverify::pre(cppverify::forall(k, 0, 8, 0 <= r->buf[k] && r->buf[k] <= 100))
  cppverify::post(cppverify::result >= 0)
{
  int s = 0;
  const int *q = r->buf;
  int i = 0;
  while (i < 8)
    cppverify::invariant(0 <= i && i <= 8 && q == r->buf + i)
    cppverify::invariant(0 <= s && s <= 100 * i)
    cppverify::decreases(8 - i)
  {
    s = s + *q;
    q = q + 1;
    i = i + 1;
  }
  return s;
}
// CHECK-DAG: Verified: sum8 [backend=z3]

int count8(const Ring *r)
  cppverify::pre(r != nullptr)
  cppverify::post(cppverify::result == 8)
{
  int n = 0;
  for (const int *q = r->buf; q != r->buf + 8; q = q + 1)
    cppverify::invariant(r->buf <= q && q <= r->buf + 8 && n == q - r->buf)
    cppverify::decreases(r->buf + 8 - q)
  {
    n = n + 1;
  }
  return n;
}
// CHECK-DAG: Verified: count8 [backend=z3]

int distance(const Ring *r, int i)
  cppverify::pre(r != nullptr && 0 <= i && i <= 8)
  cppverify::post(cppverify::result == i)
{
  const int *q = r->buf + i;
  return q - r->buf;
}
// CHECK-DAG: Verified: distance [backend=z3]

int chosen(const Ring *r, bool c)
  cppverify::pre(r != nullptr)
  cppverify::post(cppverify::result == (c ? r->buf[1] : r->other[1]))
{
  const int *q = c ? r->buf : r->other;
  return q[1];
}
// CHECK-DAG: Verified: chosen [backend=z3]

// A pointer assigned another value takes that value's bounds.
int reassigned(const Ring *r, const int *p)
  cppverify::pre(r != nullptr && p != nullptr)
  cppverify::post(cppverify::result == *p)
{
  const int *q = r->buf;
  q = p;
  return q[0];
}
// CHECK-DAG: Verified: reassigned [backend=z3]

void write_through(Ring *r, int i)
  cppverify::pre(r != nullptr && 0 <= i && i < 8)
  cppverify::modifies(r->buf[0 : 8])
  cppverify::post(r->buf[i] == 7 && r->head == cppverify::old(r->head))
{
  int *q = r->buf;
  q[i] = 7;
}
// CHECK-DAG: Verified: write_through [backend=z3]

int checked(const Ring *r)
  cppverify::pre(r != nullptr)
  cppverify::post(cppverify::result == r->buf[3])
{
  const int *q = r->buf;
  cppverify::check(q[3] == r->buf[3]);
  return q[3];
}
// CHECK-DAG: Verified: checked [backend=z3]

// Nine elements from buf run into head.
int pass_too_long(const Ring *r)
  cppverify::pre(r != nullptr)
{
  return first(r->buf, 9);
}
// CHECK-DAG: :[[@LINE-2]]:3: error: verification failed: pass_too_long [bounds]
// CHECK-DAG: note: counterexample: {{.*}}r = {{[0-9]+}}{{( ->|,|$)}}

int pass_tail_too_long(const Ring *r)
  cppverify::pre(r != nullptr)
{
  return first(r->buf + 5, 4);
}
// CHECK-DAG: :[[@LINE-2]]:3: error: verification failed: pass_tail_too_long [bounds]

// The end of buf is a pointer, but get reads the element there: r->head.
int pass_end(const Ring *r)
  cppverify::pre(r != nullptr)
{
  const int *q = r->buf + 8;
  return get(q);
}
// CHECK-DAG: :[[@LINE-2]]:3: error: verification failed: pass_end [bounds]

// q[-1] is r->items[3].w, inside *r but before other.
int before_member(const Ring *r)
  cppverify::pre(r != nullptr)
{
  const int *q = r->other;
  return q[-1];
}
// CHECK-DAG: :[[@LINE-2]]:10: error: verification failed: before_member [bounds]

// q[8] is r->head.
int local_past(const Ring *r)
  cppverify::pre(r != nullptr)
{
  const int *q = r->buf;
  return q[8];
}
// CHECK-DAG: :[[@LINE-2]]:10: error: verification failed: local_past [bounds]

int element_past(const Ring *r)
  cppverify::pre(r != nullptr)
{
  const int *q = &r->buf[2];
  return q[6];
}
// CHECK-DAG: :[[@LINE-2]]:10: error: verification failed: element_past [bounds]

// q[1] is r->inner.x, next to head.
void field_neighbor(Ring *r)
  cppverify::pre(r != nullptr)
  cppverify::modifies(*r)
{
  int *q = &r->head;
  q[1] = 0;
}
// CHECK-DAG: :[[@LINE-2]]:3: error: verification failed: field_neighbor [bounds]

// q[4] is grid[i + 1][0].
int row_past(const Ring *r, int i)
  cppverify::pre(r != nullptr && 0 <= i && i < 2)
{
  const int *q = r->grid[i];
  return q[4];
}
// CHECK-DAG: :[[@LINE-2]]:10: error: verification failed: row_past [bounds]

// it[1] is past items, at r->other.
int item_past(const Ring *r)
  cppverify::pre(r != nullptr)
{
  const Item *it = &r->items[3];
  return it[1].v;
}
// CHECK-DAG: :[[@LINE-2]]:16: error: verification failed: item_past [bounds]

// When c is false, q addresses other, of two elements.
int chosen_past(const Ring *r, bool c)
  cppverify::pre(r != nullptr)
{
  const int *q = c ? r->buf : r->other;
  return q[2];
}
// CHECK-DAG: :[[@LINE-2]]:10: error: verification failed: chosen_past [bounds]
// CHECK-DAG: note: counterexample: {{.*}}c = false{{( ->|,|$)}}

int walk_past(const Ring *r)
  cppverify::pre(r != nullptr)
{
  int s = 0;
  for (const int *q = r->buf; q != r->buf + 9; q = q + 1)
    cppverify::invariant(r->buf <= q && q <= r->buf + 9)
    cppverify::decreases(r->buf + 9 - q)
  {
    s = *q;
  }
  return s;
}
// CHECK-DAG: :[[@LINE-4]]:10: error: verification failed: walk_past [bounds]

// Forming the address of an element is reading nothing, but the element
// must exist: buf[8] does not.
int element_one_past(const Ring *r, int i)
  cppverify::pre(r != nullptr && i == 8)
{
  const int *q = &r->buf[i];
  return 0;
}
// CHECK-DAG: :[[@LINE-3]]:19: error: verification failed: element_one_past [bounds]
// CHECK-DAG: note: counterexample: {{.*}}i = 8{{( ->|,|$)}}

int null_root(const Ring *r)
  cppverify::post(cppverify::result == 0)
{
  const int *q = r->buf;
  return 0;
}
// CHECK-DAG: :[[@LINE-3]]:18: error: verification failed: null_root [dereference]
// CHECK-DAG: note: counterexample: r = 0

// Pointers into different members differ by nothing C++ defines.
int across_members(const Ring *r)
  cppverify::pre(r != nullptr)
{
  return &r->head - r->buf;
}
// CHECK-DAG: :[[@LINE-2]]:21: error: verification failed: across_members [pointer-difference]

void write_frame(Ring *r)
  cppverify::pre(r != nullptr)
  cppverify::modifies(r->buf[0 : 8])
{
  int *q = r->other;
  q[0] = 7;
}
// CHECK-DAG: :[[@LINE-2]]:8: error: verification failed: write_frame [frame]

// An operand that `&&`, `||`, or `?:` evaluates only on a path of its own
// forms its pointer, and checks it, only there.
bool same_slot(const Ring *r, int i, const int *q)
  cppverify::pre(r != nullptr && 0 <= i)
  cppverify::post(!cppverify::result || i < 8)
{
  bool same = i < 8 && &r->buf[i] == q;
  bool other = i >= 8 || &r->buf[i] != q;
  return same && !other;
}
// CHECK-DAG: Verified: same_slot [backend=z3]

void put_slot(Ring *r, int i, int v)
  cppverify::pre(r != nullptr && 0 <= i)
  cppverify::modifies(r->buf[0 : 8])
  cppverify::post(i >= 8 || r->buf[i] == v)
{
  int *q = i < 8 ? &r->buf[i] : nullptr;
  if (q != nullptr)
    *q = v;
}
// CHECK-DAG: Verified: put_slot [backend=z3]

// The pointer chosen keeps the bounds of its own path.
void put_past_slot(Ring *r, int i, int v)
  cppverify::pre(r != nullptr && 0 <= i && i < 8)
  cppverify::modifies(r->buf[0 : 8])
{
  int *q = i < 4 ? &r->buf[i] : &r->buf[7];
  q[1] = v;
}
// CHECK-DAG: :[[@LINE-2]]:3: error: verification failed: put_past_slot [bounds]
#else
// A pointer that left the function would lose its bounds.
struct Holder {
  const int *p;
};

void stored(Ring *r, Holder *h)
  cppverify::pre(r != nullptr && h != nullptr)
  cppverify::modifies(h->p)
{
  h->p = r->buf;
}
// ESCAPE-DAG: subobject_pointers.cpp:[[@LINE-2]]:8: error: stored: a pointer into a member array or field cannot be stored in memory yet

const int *returned(const Ring *r)
  cppverify::pre(r != nullptr)
{
  return &r->buf[2];
}
// ESCAPE-DAG: subobject_pointers.cpp:[[@LINE-2]]:3: error: returned: returning a pointer into a member array or field is unsupported
#endif
