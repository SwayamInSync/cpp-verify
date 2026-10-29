// RUN: not %cpp-verify --jobs=1 %s -- 2>&1 | FileCheck %s
// RUN: not %cpp-verify --jobs=1 --backend=bmc --unroll=3 %s -- 2>&1 \
// RUN:   | FileCheck %s --check-prefix=BMC
// RUN: %cpp-verify --lower-only --dump-ir=1 %s -- -DLOWER 2>&1 \
// RUN:   | FileCheck %s --check-prefix=IR
//
// An extent of a pointer field, cppverify::valid(s->data, s->len), describes
// the buffer the field addresses at entry. That entry value is an input of the
// function, as a parameter's value is: a synthetic parameter after the
// declared ones, the field's value at entry by definition, which a call binds
// to the field at its arguments. It takes the extent and its validity, and the
// default separation: a buffer through a pointer to non-const is disjoint from
// the other address parameters' objects, its own record's included.

struct Buf {
  int *data;
  int len;
};

struct View {
  const int *data;
  int len;
};

struct Pair {
  Buf in;
  Buf out;
};

void zero(Buf &b)
  cppverify::pre(cppverify::valid(b.data, b.len) && 0 <= b.len)
  cppverify::modifies(b.data[0 : b.len])
  cppverify::post(cppverify::forall(k, 0, b.len, b.data[k] == 0))
{
  for (int i = 0; i < b.len; i = i + 1)
    cppverify::invariant(0 <= i && i <= b.len)
    cppverify::invariant(cppverify::forall(k, 0, i, b.data[k] == 0))
    cppverify::modifies(b.data[0 : b.len])
    cppverify::decreases(b.len - i)
  {
    b.data[i] = 0;
  }
}
// CHECK-DAG: Verified: zero [backend=z3]
// BMC-DAG: BoundedSafe: zero [backend=bmc, bound=3]
// IR-LABEL: fn zero
// IR:       param b
// IR-NEXT:  param b->data
// IR-NEXT:  pre

#ifndef LOWER
int count(const View *v, int x)
  cppverify::pre(v != nullptr && cppverify::valid(v->data, v->len))
  cppverify::pre(0 <= v->len && v->len <= 100)
  cppverify::post(0 <= cppverify::result && cppverify::result <= v->len)
{
  int n = 0;
  for (int i = 0; i < v->len; i = i + 1)
    cppverify::invariant(0 <= i && i <= v->len && 0 <= n && n <= i)
    cppverify::decreases(v->len - i)
  {
    if (v->data[i] == x)
      n = n + 1;
  }
  return n;
}
// CHECK-DAG: Verified: count [backend=z3]

int past(const View *v)
  cppverify::pre(v != nullptr && cppverify::valid(v->data, v->len))
  cppverify::pre(v->len >= 0)
{
  return v->data[v->len];
}
// CHECK-DAG: :[[@LINE-2]]:10: error: verification failed: past [bounds]
// CHECK-DAG: note: counterexample: {{.*}}v->data =

// Without an extent the field's buffer is no object of the function's.
void unknown(Buf &b)
  cppverify::pre(b.len >= 1)
  cppverify::modifies(b.data[0 : 1])
{
  b.data[0] = 1;
}
// CHECK-DAG: :[[@LINE-2]]:3: error: verification failed: unknown [bounds]

// The buffer is disjoint from its record, so the length keeps its value.
int keeps_len(Buf &b)
  cppverify::pre(cppverify::valid(b.data, b.len) && 1 <= b.len && b.len < 100)
  cppverify::modifies(b.data[0 : b.len])
  cppverify::post(cppverify::result == cppverify::old(b.len))
{
  b.data[0] = 5;
  return b.len;
}
// CHECK-DAG: Verified: keeps_len [backend=z3]

// A field of a nested record, through a pointer.
void zero_out(Pair *p)
  cppverify::pre(p != nullptr && cppverify::valid(p->out.data, p->out.len))
  cppverify::pre(0 <= p->out.len)
  cppverify::modifies(p->out.data[0 : p->out.len])
  cppverify::post(p->out.len == cppverify::old(p->out.len))
{
  zero(p->out);
}
// CHECK-DAG: Verified: zero_out [backend=z3]

void zero_out_ref(Pair &p)
  cppverify::pre(cppverify::valid(p.out.data, p.out.len) && 0 <= p.out.len)
  cppverify::modifies(p.out.data[0 : p.out.len])
  cppverify::post(p.out.len == cppverify::old(p.out.len))
{
  zero(p.out);
}
// CHECK-DAG: Verified: zero_out_ref [backend=z3]

// At a call the field's value at the arguments has the extent: the
// caller's own field extent, or its own parameter's.
void zero_twice(Buf &b)
  cppverify::pre(cppverify::valid(b.data, b.len) && 0 <= b.len)
  cppverify::modifies(b.data[0 : b.len])
  cppverify::post(cppverify::forall(k, 0, b.len, b.data[k] == 0))
{
  zero(b);
  zero(b);
}
// CHECK-DAG: Verified: zero_twice [backend=z3]

void from_param(int *p, int n)
  cppverify::pre(cppverify::valid(p, n) && 0 <= n)
  cppverify::modifies(p[0 : n])
  cppverify::post(cppverify::forall(k, 0, n, p[k] == 0))
{
  Buf b;
  b.data = p;
  b.len = n;
  zero(b);
}
// CHECK-DAG: Verified: from_param [backend=z3]

void too_long(int *p, int n)
  cppverify::pre(cppverify::valid(p, n) && 0 <= n && n < 100)
  cppverify::modifies(p[0 : n])
{
  Buf b;
  b.data = p;
  b.len = n + 1;
  zero(b);
}
// CHECK-DAG: :[[@LINE-2]]:3: error: verification failed: too_long [bounds]
// BMC-DAG: :[[@LINE-3]]:3: error: verification failed: too_long [bounds]

// The extent is the field's at entry: a field given another pointer
// addresses that pointer's object.
void reseat(Buf &b, int *other)
  cppverify::pre(cppverify::valid(b.data, b.len) && 1 <= b.len)
  cppverify::pre(other != nullptr)
  cppverify::modifies(b.data, *other)
{
  b.data = other;
  b.data[0] = 1;
}
// CHECK-DAG: Verified: reseat [backend=z3]

void reseat_past(Buf &b, int *other)
  cppverify::pre(cppverify::valid(b.data, b.len) && 2 <= b.len)
  cppverify::pre(other != nullptr)
  cppverify::modifies(b.data, *other)
{
  b.data = other;
  b.data[1] = 1;
}
// CHECK-DAG: :[[@LINE-2]]:3: error: verification failed: reseat_past [bounds]

// Two mutable buffers are disjoint by default, as two mutable parameters
// are; two read-only ones may be one.
void copy(Buf &dst, const Buf &src)
  cppverify::pre(cppverify::valid(dst.data, dst.len))
  cppverify::pre(cppverify::valid(src.data, src.len))
  cppverify::pre(0 <= dst.len && dst.len <= src.len)
  cppverify::modifies(dst.data[0 : dst.len])
  cppverify::post(cppverify::forall(k, 0, dst.len, dst.data[k] == src.data[k]))
{
  for (int i = 0; i < dst.len; i = i + 1)
    cppverify::invariant(0 <= i && i <= dst.len)
    cppverify::invariant(cppverify::forall(k, 0, i, dst.data[k] == src.data[k]))
    cppverify::modifies(dst.data[0 : dst.len])
    cppverify::decreases(dst.len - i)
  {
    dst.data[i] = src.data[i];
  }
}
// CHECK-DAG: Verified: copy [backend=z3]

void self_copy(Buf &b)
  cppverify::pre(cppverify::valid(b.data, b.len) && 0 <= b.len)
  cppverify::modifies(b.data[0 : b.len])
{
  copy(b, b);
}
// CHECK-DAG: :[[@LINE-2]]:3: error: verification failed: self_copy [aliasing]
// CHECK-DAG: note: counterexample: {{.*}}b.data =

int first_of_both(const View &a, const View &b)
  cppverify::pre(cppverify::valid(a.data, a.len) && cppverify::valid(b.data, b.len))
  cppverify::pre(a.len >= 1 && b.len >= 1)
  cppverify::pre(-1000 < a.data[0] && a.data[0] < 1000)
  cppverify::pre(-1000 < b.data[0] && b.data[0] < 1000)
  cppverify::post(cppverify::result == a.data[0] + b.data[0])
{
  return a.data[0] + b.data[0];
}

int first_twice(const View &a)
  cppverify::pre(cppverify::valid(a.data, a.len) && a.len >= 1)
  cppverify::pre(-1000 < a.data[0] && a.data[0] < 1000)
  cppverify::post(cppverify::result == 2 * a.data[0])
{
  return first_of_both(a, a);
}
// CHECK-DAG: Verified: first_twice [backend=z3]

// A pair with an extent is separated over its extents: an empty one may lie
// in another object, which no access through it reads. Before, the
// one-object separation of the pair was required as well.
void touch(Buf *b, int *p, int n)
  cppverify::pre(b != nullptr && cppverify::valid(p, n) && 0 <= n)
  cppverify::modifies(b->len)
{
  b->len = 0;
}

void empty_inside(Buf *b)
  cppverify::pre(b != nullptr)
  cppverify::modifies(b->len)
{
  touch(b, &b->len, 0);
}
// CHECK-DAG: Verified: empty_inside [backend=z3]

void nonempty_inside(Buf *b)
  cppverify::pre(b != nullptr)
  cppverify::modifies(b->len)
{
  touch(b, &b->len, 1);
}
// CHECK-DAG: :[[@LINE-2]]:3: error: verification failed: nonempty_inside [aliasing]

// Not yet: a field of an element (s->items[k].data).
struct Shelf {
  View items[2];
};

int shelf_first(const Shelf *s)
  cppverify::pre(s != nullptr && cppverify::valid(s->items[0].data, s->items[0].len))
{
  return 0;
}
// CHECK-DAG: error: shelf_first: valid marker requires a bare complete-object pointer and an integer element count
#endif
