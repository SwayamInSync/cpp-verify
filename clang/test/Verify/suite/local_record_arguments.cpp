// RUN: not %cpp-verify --jobs=1 %s -- 2>&1 | FileCheck %s
// RUN: not %cpp-verify --jobs=1 --backend=bmc --unroll=5 %s -- 2>&1 \
// RUN:   | FileCheck %s --check-prefix=BMC
// RUN: not %cpp-verify --jobs=1 --no-check-ub %s -- 2>&1 \
// RUN:   | FileCheck %s --check-prefix=NOUB
// RUN: %cpp-verify --lower-only --dump-ir=2 %s -- -DLOWER 2>&1 \
// RUN:   | FileCheck %s --check-prefix=PASSIVE
//
// A local record passed to a callee by reference, or by its address, keeps
// its lifetime and frame across the call. The callee is verified in the
// object model, so every access through its parameter, at any field or
// element, lies in the object; the call checks that the callee keeps no
// address of it (stores none, returns none, frees none, and passes it only to
// callees that keep none), that the whole record lies in the live object, and
// that every field is initialized. The callee then writes only its footprints
// in the record, by their bytes.

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

void bump(Counter &c)
  cppverify::pre(c.n < c.limit)
  cppverify::modifies(c.n)
  cppverify::post(c.n == cppverify::old(c.n) + 1)
  cppverify::post(c.limit == cppverify::old(c.limit))
{
  c.n = c.n + 1;
}
// CHECK-DAG: Verified: bump [backend=z3]

void reset(Counter *c)
  cppverify::pre(c != nullptr)
  cppverify::modifies(*c)
  cppverify::post(c->n == 0 && c->limit == 10)
{
  c->n = 0;
  c->limit = 10;
}

int by_reference()
  cppverify::post(cppverify::result == 1)
{
  Counter c;
  c.n = 0;
  c.limit = 5;
  bump(c);
  return c.n;
}
// CHECK-DAG: Verified: by_reference [backend=z3]
// BMC-DAG: Verified: by_reference [backend=bmc, bound=0]
// NOUB-DAG: Unresolved: by_reference [backend=z3] [reason=construct.unsupported] (the verifier cannot model a construct here: the address of local or dynamic storage is passed to bump, which may keep, offset, or free it, or has no verified body)
// The generated clauses name the first byte; the call checks the last byte
// and every field.
// PASSIVE-LABEL: passive by_reference
// PASSIVE:      assert precondition
// PASSIVE:      assert pointer-validity
// PASSIVE:      assert unsupported
// PASSIVE:      assert pointer-validity
// PASSIVE-NEXT:   ||
// PASSIVE-NEXT:     !
// PASSIVE-NEXT:       true
// PASSIVE-NEXT:     valid_ptr
// PASSIVE-NEXT:       +
// PASSIVE-NEXT:         c_{{[0-9]+}}
// PASSIVE-NEXT:         7
// PASSIVE-NEXT: assert unsupported
// PASSIVE-NEXT:   ||
// PASSIVE-NEXT:     !
// PASSIVE-NEXT:       true
// PASSIVE-NEXT:     &&
// PASSIVE-NEXT:       initialized_ptr
// PASSIVE-NEXT:         +
// PASSIVE-NEXT:           c_{{[0-9]+}}
// PASSIVE-NEXT:           0
// PASSIVE-NEXT:       initialized_ptr
// PASSIVE-NEXT:         +
// PASSIVE-NEXT:           c_{{[0-9]+}}
// PASSIVE-NEXT:           4

#ifndef LOWER
int keeps_limit()
  cppverify::post(cppverify::result == 5)
{
  Counter c;
  c.n = 0;
  c.limit = 5;
  bump(c);
  return c.limit;
}
// CHECK-DAG: Verified: keeps_limit [backend=z3]

int by_address()
  cppverify::post(cppverify::result == 10)
{
  Counter c;
  c.n = 3;
  c.limit = 4;
  reset(&c);
  return c.limit;
}
// CHECK-DAG: Verified: by_address [backend=z3]

int other_local()
  cppverify::post(cppverify::result == 4)
{
  Counter c;
  c.n = 0;
  c.limit = 5;
  int k = 4;
  bump(c);
  return k;
}
// CHECK-DAG: Verified: other_local [backend=z3]

int wrong()
  cppverify::post(cppverify::result == 5)
{
  Counter c;
  c.n = 0;
  c.limit = 5;
  bump(c);
  return c.n;
}
// CHECK-DAG: :[[@LINE-8]]:37: error: verification failed: wrong [postcondition]
// CHECK-DAG: note: counterexample: {{.*}}result = 1{{( ->|,|$)}}

// A member and an element of a local, and the address of a field.
int member()
  cppverify::post(cppverify::result == 7)
{
  Pair p;
  p.left.n = 0;
  p.left.limit = 5;
  p.right.n = 7;
  p.right.limit = 9;
  bump(p.left);
  return p.right.n;
}
// CHECK-DAG: Verified: member [backend=z3]

int element()
  cppverify::post(cppverify::result == 1)
{
  Counter a[2];
  a[0].n = 0;
  a[0].limit = 3;
  a[1].n = 0;
  a[1].limit = 3;
  bump(a[1]);
  return a[1].n - a[0].n;
}
// CHECK-DAG: Verified: element [backend=z3]

void inc(int *p)
  cppverify::pre(p != nullptr && *p < 100)
  cppverify::modifies(*p)
  cppverify::post(*p == cppverify::old(*p) + 1)
{
  *p = *p + 1;
}

int field_address()
  cppverify::post(cppverify::result == 1)
{
  Counter c;
  c.n = 0;
  c.limit = 1;
  inc(&c.n);
  return c.n;
}
// CHECK-DAG: Verified: field_address [backend=z3]

int scalar_address()
  cppverify::post(cppverify::result == 2)
{
  int x = 1;
  inc(&x);
  return x;
}
// CHECK-DAG: Verified: scalar_address [backend=z3]

// The callee may reach the record through copies of the address, forward it
// to callees that keep none, and recurse.
void twice(Counter &c)
  cppverify::pre(c.n + 1 < c.limit)
  cppverify::modifies(c.n)
  cppverify::post(c.n == cppverify::old(c.n) + 2)
{
  bump(c);
  bump(c);
}

int nested_calls()
  cppverify::post(cppverify::result == 2)
{
  Counter c;
  c.n = 0;
  c.limit = 5;
  twice(c);
  return c.n;
}
// CHECK-DAG: Verified: nested_calls [backend=z3]

void walk(Ring &r)
  cppverify::modifies(r.buf[0 : 4])
  cppverify::post(cppverify::forall(k, 0, 4, r.buf[k] == 0))
{
  for (int *q = r.buf; q != r.buf + 4; q = q + 1)
    cppverify::invariant(r.buf <= q && q <= r.buf + 4)
    cppverify::invariant(cppverify::forall(k, 0, q - r.buf, r.buf[k] == 0))
    cppverify::decreases(r.buf + 4 - q)
  {
    *q = 0;
  }
}

int walked()
  cppverify::post(cppverify::result == 5)
{
  Ring r;
  r.buf[0] = 1;
  r.buf[1] = 2;
  r.buf[2] = 3;
  r.buf[3] = 4;
  r.head = 5;
  walk(r);
  return r.buf[3] + r.head;
}
// CHECK-DAG: Verified: walked [backend=z3]

void first_to(int *q, int v)
  cppverify::pre(cppverify::valid(q, 4))
  cppverify::modifies(q[0])
  cppverify::post(q[0] == v)
{
  q[0] = v;
}

void through_decay(Ring &r)
  cppverify::modifies(r.buf[0])
  cppverify::post(r.buf[0] == 7)
{
  first_to(r.buf, 7);
}

int decayed()
  cppverify::post(cppverify::result == 7)
{
  Ring r;
  r.buf[0] = 1;
  r.buf[1] = 2;
  r.buf[2] = 3;
  r.buf[3] = 4;
  r.head = 2;
  through_decay(r);
  return r.buf[0];
}
// CHECK-DAG: Verified: decayed [backend=z3]

void down(Counter &c, int k)
  cppverify::pre(k >= 0)
  cppverify::modifies(c.n)
  cppverify::decreases(k)
{
  c.n = k;
  if (k > 0)
    down(c, k - 1);
}

int recursive()
  cppverify::post(cppverify::result == 9)
{
  Counter c;
  c.n = 3;
  c.limit = 9;
  down(c, 3);
  return c.limit;
}
// CHECK-DAG: Verified: recursive [backend=z3]

// A range footprint in the caller's own object: before, the range's check
// that it may be empty replaced the check that the object is the caller's.
void clear(Ring &r)
  cppverify::modifies(r.buf[0 : 4], r.head)
  cppverify::post(r.head == 0 && cppverify::forall(k, 0, 4, r.buf[k] == 0))
{
  for (int i = 0; i < 4; i = i + 1)
    cppverify::invariant(0 <= i && i <= 4)
    cppverify::invariant(cppverify::forall(k, 0, i, r.buf[k] == 0))
    cppverify::modifies(r.buf[0 : 4])
    cppverify::decreases(4 - i)
  {
    r.buf[i] = 0;
  }
  r.head = 0;
}

int cleared()
  cppverify::post(cppverify::result == 0)
{
  Ring r;
  r.buf[0] = 1;
  r.buf[1] = 2;
  r.buf[2] = 3;
  r.buf[3] = 4;
  r.head = 2;
  clear(r);
  return r.buf[2] + r.head;
}
// CHECK-DAG: Verified: cleared [backend=z3]

// The caller's own frame need not name its local.
void into_out(int *out)
  cppverify::pre(out != nullptr)
  cppverify::modifies(*out)
  cppverify::post(*out == 1)
{
  Counter c;
  c.n = 0;
  c.limit = 5;
  bump(c);
  *out = c.n;
}
// CHECK-DAG: Verified: into_out [backend=z3]

// Two locals are distinct objects; one passed twice is not.
void pair_bump(Counter &a, Counter &b)
  cppverify::pre(a.n < 10 && b.n < 10)
  cppverify::modifies(a.n, b.n)
  cppverify::post(a.n == cppverify::old(a.n) + 1)
  cppverify::post(b.n == cppverify::old(b.n) + 1)
{
  a.n = a.n + 1;
  b.n = b.n + 1;
}

int two_locals()
  cppverify::post(cppverify::result == 2)
{
  Counter a;
  a.n = 0;
  a.limit = 0;
  Counter b;
  b.n = 0;
  b.limit = 0;
  pair_bump(a, b);
  return a.n + b.n;
}
// CHECK-DAG: Verified: two_locals [backend=z3]

int same_local()
  cppverify::post(cppverify::result == 2)
{
  Counter a;
  a.n = 0;
  a.limit = 0;
  pair_bump(a, a);
  return a.n;
}
// CHECK-DAG: :[[@LINE-3]]:3: error: verification failed: same_local [aliasing]

// A callee that writes its record before reading it needs none of it
// initialized: c.limit never is. One that may read it needs every field.
void set_n(Counter &c)
  cppverify::modifies(c.n)
  cppverify::post(c.n == 1)
{
  c.n = 1;
}

int out_parameter()
  cppverify::post(cppverify::result == 1)
{
  Counter c;
  c.n = 0;
  set_n(c);
  return c.n;
}
// CHECK-DAG: Verified: out_parameter [backend=z3]

int get_n(const Counter &c)
  cppverify::post(cppverify::result == c.n)
{
  return c.n;
}

int partly_initialized()
  cppverify::post(cppverify::result == 0)
{
  Counter c;
  c.n = 0;
  return get_n(c);
}
// CHECK-DAG: [[@LINE-2]]:3: Unresolved: partly_initialized [backend=z3] [reason=construct.unsupported] (the verifier cannot model a construct here: binding a reference or pointer parameter to storage that is not initialized, which the callee may read before writing it)

// A callee that keeps the address: in memory, or by returning it.
struct Node {
  Node *self;
  int v;
};

void selfref(Node &n)
  cppverify::modifies(n.self)
{
  n.self = &n;
}

int keeps_self()
  cppverify::post(cppverify::result == 0)
{
  Node n;
  n.self = nullptr;
  n.v = 0;
  selfref(n);
  return 0;
}
// CHECK-DAG: [[@LINE-3]]:3: Unresolved: keeps_self [backend=z3] [reason=construct.unsupported] (the verifier cannot model a construct here: the address of local or dynamic storage is passed to selfref, which may keep or free it, or has no verified body)

Counter *same(Counter *p)
  cppverify::post(cppverify::result == p)
{
  return p;
}

int returned()
  cppverify::post(cppverify::result == 0)
{
  Counter c;
  c.n = 0;
  c.limit = 1;
  Counter *q = same(&c);
  return 0;
}
// CHECK-DAG: [[@LINE-3]]:3: Unresolved: returned [backend=z3] [reason=construct.unsupported] (the verifier cannot model a construct here: the address of local or dynamic storage is passed to same, which may keep or free it, or has no verified body)

// A copy of the address is the address, and so is one passed on.
void keeps_copy(Node &n)
  cppverify::modifies(n.self)
{
  Node *q = &n;
  n.self = q;
}

int copied()
  cppverify::post(cppverify::result == 0)
{
  Node n;
  n.self = nullptr;
  n.v = 0;
  keeps_copy(n);
  return 0;
}
// CHECK-DAG: [[@LINE-3]]:3: Unresolved: copied [backend=z3] [reason=construct.unsupported] (the verifier cannot model a construct here: the address of local or dynamic storage is passed to keeps_copy, which may keep or free it, or has no verified body)

void forwards(Node &n)
  cppverify::modifies(n.self)
{
  selfref(n);
}

int forwarded()
  cppverify::post(cppverify::result == 0)
{
  Node n;
  n.self = nullptr;
  n.v = 0;
  forwards(n);
  return 0;
}
// CHECK-DAG: [[@LINE-3]]:3: Unresolved: forwarded [backend=z3] [reason=construct.unsupported] (the verifier cannot model a construct here: the address of local or dynamic storage is passed to forwards, which may keep or free it, or has no verified body)

// An extent is not offered to a local: zero_two may write c and the record
// after it.
void zero_two(Counter *a, int n)
  cppverify::pre(cppverify::valid(a, n) && 0 <= n && n <= 2)
  cppverify::modifies(*a)
{
  for (int i = 0; i < n; i = i + 1)
    cppverify::invariant(0 <= i && i <= n)
    cppverify::decreases(n - i)
  {
    a[i].n = 0;
  }
}

int extent_two()
  cppverify::post(cppverify::result == 0)
{
  Counter c;
  c.n = 0;
  c.limit = 1;
  zero_two(&c, 2);
  return 0;
}
// CHECK-DAG: [[@LINE-3]]:3: Unresolved: extent_two [backend=z3] [reason=construct.unsupported] (the verifier cannot model a construct here: the address of local or dynamic storage is passed to zero_two, which may keep or free it, or has no verified body)

// A callee without a verified body, called directly or through another.
void opaque(Counter &c)
  cppverify::modifies(c.n);

void through_opaque(Counter &c)
  cppverify::modifies(c.n)
{
  opaque(c);
}

int nested_opaque()
  cppverify::post(cppverify::result == 0)
{
  Counter c;
  c.n = 0;
  c.limit = 1;
  through_opaque(c);
  return 0;
}
// CHECK-DAG: [[@LINE-3]]:3: Unresolved: nested_opaque [backend=z3] [reason=construct.unsupported] (the verifier cannot model a construct here: the address of local or dynamic storage is passed to through_opaque, which may keep or free it, or has no verified body)

int to_opaque()
  cppverify::post(cppverify::result == 0)
{
  Counter c;
  c.n = 0;
  c.limit = 1;
  opaque(c);
  return 0;
}
// CHECK-DAG: [[@LINE-3]]:3: Unresolved: to_opaque [backend=z3] [reason=construct.unsupported] (the verifier cannot model a construct here: the address of local or dynamic storage is passed to opaque, which may keep or free it, or has no verified body)
#endif
