// RUN: not %cpp-verify --jobs=1 %s -- 2>&1 | FileCheck %s
// RUN: %cpp-verify --lower-only --no-check-ub --dump-ir=1 %s -- 2>&1 \
// RUN:   | FileCheck %s --check-prefix=VCR
//
// Fields and fixed-array elements inside the object a pointer addresses, at
// any depth. Each index is bounded by its own array, so an index one past an
// array fails though its address is still inside the object.

struct Inner {
  int x;
  int y;
  int arr[4];
};

struct Item {
  int v;
  int w;
};

struct Outer {
  int buf[8];
  Inner inner;
  int grid[3][4];
  Item items[5];
};

struct Ring {
  int buf[8];
  int head;
  int count;
};

int peek(const Ring *r)
  cppverify::pre(r != nullptr && 0 <= r->head && r->head < 8)
  cppverify::post(cppverify::result == r->buf[r->head])
{
  return r->buf[r->head];
}
// CHECK-DAG: Verified: peek [backend=z3]
// VCR-LABEL: fn peek
// VCR:      return
// VCR-NEXT:   load
// VCR-NEXT:     +
// VCR-NEXT:       +
// VCR-NEXT:         r
// VCR-NEXT:         0
// VCR-NEXT:       *
// VCR-NEXT:         cast
// VCR-NEXT:           load
// VCR-NEXT:             +
// VCR-NEXT:               r
// VCR-NEXT:               32
// VCR-NEXT:         4
// VCR-NEXT:     access_condition
// VCR-NEXT:       &&
// VCR-NEXT:         >=
// VCR:            <
// VCR:                    32
// VCR-NEXT:           8

void put(Ring *r, int v)
  cppverify::pre(r != nullptr && 0 <= r->head && r->head < 8)
  cppverify::modifies(r->buf[r->head])
  cppverify::post(r->buf[r->head] == v)
  cppverify::post(r->head == cppverify::old(r->head))
  cppverify::post(r->count == cppverify::old(r->count))
{
  r->buf[r->head] = v;
}
// CHECK-DAG: Verified: put [backend=z3]

// A reference bound to an element, and an element passed by reference.
void put_ref(Ring *r, int v)
  cppverify::pre(r != nullptr && 0 <= r->head && r->head < 8)
  cppverify::modifies(r->buf[r->head])
  cppverify::post(r->buf[r->head] == v)
{
  int &slot = r->buf[r->head];
  slot = v;
}
// CHECK-DAG: Verified: put_ref [backend=z3]

void bump(int &x)
  cppverify::pre(x < 100)
  cppverify::modifies(x)
  cppverify::post(x == cppverify::old(x) + 1)
{
  x = x + 1;
}
// CHECK-DAG: Verified: bump [backend=z3]

void bump_slot(Ring *r, int i)
  cppverify::pre(r != nullptr && 0 <= i && i < 8 && r->buf[i] < 100)
  cppverify::modifies(r->buf[i])
  cppverify::post(r->buf[i] == cppverify::old(r->buf[i]) + 1)
  cppverify::post(r->head == cppverify::old(r->head))
{
  bump(r->buf[i]);
}
// CHECK-DAG: Verified: bump_slot [backend=z3]

int nested(const Outer *p, int i, int j, int k)
  cppverify::pre(p != nullptr && 0 <= i && i < 3 && 0 <= j && j < 4)
  cppverify::pre(0 <= k && k < 5)
  cppverify::pre(0 <= p->inner.y && p->inner.y < 1000)
  cppverify::pre(0 <= p->inner.arr[j] && p->inner.arr[j] < 1000)
  cppverify::pre(0 <= p->grid[i][j] && p->grid[i][j] < 1000)
  cppverify::pre(0 <= p->items[k].v && p->items[k].v < 1000)
  cppverify::post(cppverify::result == p->inner.y + p->inner.arr[j] +
                                           p->grid[i][j] + p->items[k].v)
{
  return p->inner.y + p->inner.arr[j] + p->grid[i][j] + (*p).items[k].v;
}
// CHECK-DAG: Verified: nested [backend=z3]

// p[k] is an element of the extent; buf[i] an element of its array.
int element_of_extent(const Outer *p, int n, int k, int i)
  cppverify::pre(cppverify::valid(p, n) && 0 <= k && k < n)
  cppverify::pre(0 <= i && i < 8)
  cppverify::post(cppverify::result == p[k].buf[i])
{
  return p[k].buf[i];
}
// CHECK-DAG: Verified: element_of_extent [backend=z3]

void nested_write(Outer *p)
  cppverify::pre(p != nullptr)
  cppverify::modifies(p->inner.y)
  cppverify::post(p->inner.y == 3 && p->inner.x == cppverify::old(p->inner.x))
{
  p->inner.y = 3;
}
// CHECK-DAG: Verified: nested_write [backend=z3]

void write_keeps_others(Outer *p, int i, int j)
  cppverify::pre(p != nullptr && 0 <= i && i < 8 && 0 <= j && j < 8 && i != j)
  cppverify::modifies(p->buf[i])
  cppverify::post(p->buf[j] == cppverify::old(p->buf[j]))
  cppverify::post(p->inner.x == cppverify::old(p->inner.x))
{
  p->buf[i] = 5;
}
// CHECK-DAG: Verified: write_keeps_others [backend=z3]

void clear(Outer *p)
  cppverify::pre(p != nullptr)
  cppverify::modifies(p->buf[0 : 8])
  cppverify::post(cppverify::forall(k, 0, 8, p->buf[k] == 0))
  cppverify::post(p->inner.y == cppverify::old(p->inner.y))
{
  for (int i = 0; i < 8; i = i + 1)
    cppverify::invariant(0 <= i && i <= 8)
    cppverify::invariant(cppverify::forall(k, 0, i, p->buf[k] == 0))
    cppverify::modifies(p->buf[0 : 8])
    cppverify::decreases(8 - i)
  {
    p->buf[i] = 0;
  }
}
// CHECK-DAG: Verified: clear [backend=z3]

int clear_then_read(Outer *p)
  cppverify::pre(p != nullptr)
  cppverify::modifies(p->buf[0 : 8])
  cppverify::post(cppverify::result == 0)
{
  int before = p->inner.y;
  clear(p);
  cppverify::check(p->inner.y == before);
  return p->buf[3];
}
// CHECK-DAG: Verified: clear_then_read [backend=z3]

// A spec reads the elements through the pointer, in the state of each call.
cppverify::spec int total(const Ring *r, int n)
  cppverify::decreases(n)
{
  return n <= 0 ? 0 : total(r, n - 1) + r->buf[n - 1];
}
// CHECK-DAG: Verified: spec decreases: total

int first_two(const Ring *r)
  cppverify::pre(r != nullptr && 0 <= r->buf[0] && r->buf[0] < 1000)
  cppverify::pre(0 <= r->buf[1] && r->buf[1] < 1000)
  cppverify::post(cppverify::result == total(r, 2))
{
  return r->buf[0] + r->buf[1];
}
// CHECK-DAG: Verified: first_two [backend=z3]

void set_first(Ring *r)
  cppverify::pre(r != nullptr)
  cppverify::modifies(r->buf[0])
  cppverify::post(total(r, 1) == 5)
{
  r->buf[0] = 5;
}
// CHECK-DAG: Verified: set_first [backend=z3]

// One past the array: the address is p->inner.x, inside *p.
int past_end(const Outer *p, int i)
  cppverify::pre(p != nullptr && 0 <= i && i <= 8)
{
  return p->buf[i];
}
// CHECK-DAG: :[[@LINE-2]]:10: error: verification failed: past_end [bounds]
// CHECK-DAG: note: counterexample: {{.*}}i = 8{{( ->|,|$)}}

int below_zero(const Outer *p, int i)
  cppverify::pre(p != nullptr && -1 <= i && i < 8)
{
  return p->buf[i];
}
// CHECK-DAG: :[[@LINE-2]]:10: error: verification failed: below_zero [bounds]
// CHECK-DAG: note: counterexample: {{.*}}i = -1{{( ->|,|$)}}

// A postcondition's reads are checked like the body's.
int post_past_end(const Ring *r, int i)
  cppverify::pre(r != nullptr && 0 <= i && i <= 8)
  cppverify::post(r->buf[i] >= cppverify::result || r->buf[i] < cppverify::result)
{
  return 0;
}
// CHECK-DAG: :[[@LINE-4]]:19: error: verification failed: post_past_end [bounds]
// CHECK-DAG: note: counterexample: {{.*}}i = 8{{( ->|,|$)}}

// grid[i][4] is grid[i + 1][0] in memory, but j indexes a row of 4.
int row_overflow(const Outer *p, int i, int j)
  cppverify::pre(p != nullptr && 0 <= i && i < 3 && 0 <= j && j <= 4)
{
  return p->grid[i][j];
}
// CHECK-DAG: :[[@LINE-2]]:10: error: verification failed: row_overflow [bounds]
// CHECK-DAG: note: counterexample: {{.*}}i = {{[0-2]}}{{( ->|,|$)}}{{.*}}j = 4{{( ->|,|$)}}

void store_past_end(Outer *p, int i)
  cppverify::pre(p != nullptr && 0 <= i && i <= 8)
  cppverify::modifies(*p)
{
  p->buf[i] = 0;
}
// CHECK-DAG: :[[@LINE-2]]:3: error: verification failed: store_past_end [bounds]
// CHECK-DAG: note: counterexample: {{.*}}i = 8{{( ->|,|$)}}

void slot_past_end(Ring *r, int i)
  cppverify::pre(r != nullptr && 0 <= i && i <= 8)
  cppverify::modifies(*r)
{
  int &slot = r->buf[i];
  slot = 0;
}
// CHECK-DAG: :[[@LINE-3]]:15: error: verification failed: slot_past_end [bounds]
// CHECK-DAG: note: counterexample: {{.*}}i = 8{{( ->|,|$)}}

void bump_past_end(Ring *r, int i)
  cppverify::pre(r != nullptr && 0 <= i && i <= 8 && r->head < 100)
  cppverify::modifies(*r)
{
  bump(r->buf[i]);
}
// CHECK-DAG: :[[@LINE-2]]:8: error: verification failed: bump_past_end [bounds]
// CHECK-DAG: note: counterexample: {{.*}}i = 8{{( ->|,|$)}}

// A write to buf[i] may be the read of buf[j].
void write_keeps_all(Outer *p, int i, int j)
  cppverify::pre(p != nullptr && 0 <= i && i < 8 && 0 <= j && j < 8)
  cppverify::modifies(p->buf[i])
  cppverify::post(p->buf[j] == cppverify::old(p->buf[j]))
{
  p->buf[i] = 7;
}
// CHECK-DAG: :[[@LINE-4]]:29: error: verification failed: write_keeps_all [postcondition]
// CHECK-DAG: note: counterexample: {{.*}}i = [[I:[0-7]]]{{.*}}j = [[I]]{{( ->|,|$)}}

void outside_frame(Outer *p, int i)
  cppverify::pre(p != nullptr && 0 <= i && i < 8)
  cppverify::modifies(p->inner.x)
{
  p->buf[i] = 0;
}
// CHECK-DAG: :[[@LINE-2]]:13: error: verification failed: outside_frame [frame]

void nested_write_wrong(Outer *p)
  cppverify::pre(p != nullptr)
  cppverify::modifies(p->inner.y)
  cppverify::post(p->inner.y == cppverify::old(p->inner.y))
{
  p->inner.y = 3;
}
// CHECK-DAG: :[[@LINE-4]]:30: error: verification failed: nested_write_wrong [postcondition]
// Arrays in global storage are objects too: each index is bounded by its
// array.
Ring global_ring;
int global_table[4];

int global_member(int i)
  cppverify::pre(0 <= i && i < 8)
{
  return global_ring.buf[i];
}
// CHECK-DAG: Verified: global_member

int global_array(int i)
  cppverify::pre(0 <= i && i < 4)
{
  return global_table[i];
}
// CHECK-DAG: Verified: global_array
