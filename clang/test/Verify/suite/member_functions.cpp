// RUN: not %cpp-verify --jobs=1 %s -- 2>&1 | FileCheck %s
// RUN: not %cpp-verify --jobs=1 --backend=bmc --unroll=4 %s -- 2>&1 \
// RUN:   | FileCheck %s --check-prefix=BMC
// RUN: not %cpp-verify --backend=lean --lean-out=%t.lean %s -- 2>&1 \
// RUN:   | FileCheck %s --check-prefix=LEAN
//
// A member function is a function of `this`, a pointer to its object that is
// never null, as a reference is: its fields, written f or this->f, are cells
// of the object, and a call on an object passes the object's address. Its
// clauses are in the complete-class context, so they name members declared
// after them. A non-const member function without modifies may write its
// object (decision Q8), a const one only its own storage.

struct Counter {
  void bump()
    cppverify::pre(n < limit)
    cppverify::modifies(n)
    cppverify::post(n == cppverify::old(n) + 1)
    cppverify::post(limit == cppverify::old(limit))
  {
    n = n + 1;
  }

  int get() const
    cppverify::post(cppverify::result == n)
  {
    return n;
  }

  // No modifies: the whole object.
  void reset()
    cppverify::post(n == 0 && this->limit == 10)
  {
    n = 0;
    limit = 10;
  }

  void twice()
    cppverify::pre(n + 1 < limit)
    cppverify::modifies(n)
    cppverify::post(n == cppverify::old(n) + 2)
  {
    bump();
    this->bump();
  }

  void copy_from(const Counter &o)
    cppverify::modifies(n)
    cppverify::post(n == o.n)
  {
    n = o.n;
  }

  void copy_aliased(const Counter &o)
    cppverify::aliases(this, o)
    cppverify::modifies(n)
    cppverify::post(n == cppverify::old(o.n))
  {
    n = o.n;
  }

  void bad()
    cppverify::modifies(n)
  {
    limit = 0;
  }

  int peek_counted() const
    cppverify::modifies(hits)
    cppverify::post(cppverify::result == n)
  {
    hits = 0;
    return n;
  }

  int peek_bad() const
    cppverify::post(cppverify::result == n)
  {
    hits = 0;
    return n;
  }

  static int zero()
    cppverify::post(cppverify::result == 0)
  {
    return 0;
  }

  // A const member function reads its object, which another read-only
  // parameter may share.
  int plus(const Counter &o) const
    cppverify::pre(-1000 < n && n < 1000 && -1000 < o.n && o.n < 1000)
    cppverify::post(cppverify::result == n + o.n)
  {
    return n + o.n;
  }

  // Declared here, defined below with the contract written here.
  void set(int v)
    cppverify::modifies(n)
    cppverify::post(n == v);

  int doubled() const;

  int n;
  int limit;
  mutable int hits;
};
// CHECK-DAG: Verified: Counter::bump [backend=z3]
// BMC-DAG: Verified: Counter::bump [backend=bmc, bound=0]
// LEAN-DAG: Exported: lean obligation: Counter::bump
// CHECK-DAG: Verified: Counter::get [backend=z3]
// CHECK-DAG: Verified: Counter::reset [backend=z3]
// CHECK-DAG: Verified: Counter::twice [backend=z3]
// CHECK-DAG: Verified: Counter::copy_from [backend=z3]
// CHECK-DAG: Verified: Counter::copy_aliased [backend=z3]
// CHECK-DAG: Verified: Counter::peek_counted [backend=z3]
// CHECK-DAG: Verified: Counter::zero [backend=z3]

// CHECK-DAG: :{{[0-9]+}}:11: error: verification failed: Counter::bad [frame]
// CHECK-DAG: note: counterexample: {{.*}}this =
// A const member function writes only its own storage, mutable fields
// included, unless its modifies lists them.
// CHECK-DAG: error: verification failed: Counter::peek_bad [frame]

void Counter::set(int v)
{
  n = v;
}
// CHECK-DAG: Verified: Counter::set [backend=z3]

int Counter::doubled() const
  cppverify::pre(-1000 < n && n < 1000)
  cppverify::post(cppverify::result == 2 * n)
{
  return n + get();
}
// CHECK-DAG: Verified: Counter::doubled [backend=z3]

// Calls on a local object, through a pointer, through a reference, and on
// a member of an object.
int use_local()
  cppverify::post(cppverify::result == 11)
{
  Counter c;
  c.n = 0;
  c.limit = 5;
  c.hits = 0;
  c.bump();
  int k = c.get();
  c.reset();
  return k + c.limit;
}
// CHECK-DAG: Verified: use_local [backend=z3]
// BMC-DAG: Verified: use_local [backend=bmc, bound=0]

void through_pointer(Counter *p)
  cppverify::pre(p != nullptr && p->n < p->limit)
  cppverify::modifies(p->n)
  cppverify::post(p->n == cppverify::old(p->n) + 1)
{
  p->bump();
}
// CHECK-DAG: Verified: through_pointer [backend=z3]

void through_reference(Counter &c)
  cppverify::pre(c.n < c.limit)
  cppverify::modifies(c.n)
  cppverify::post(c.n == cppverify::old(c.n) + 1)
{
  c.bump();
}
// CHECK-DAG: Verified: through_reference [backend=z3]

struct Pair {
  Counter left;
  Counter right;
};

void member_of(Pair &q)
  cppverify::modifies(q.left.n)
  cppverify::post(q.left.n == cppverify::old(q.right.n))
{
  q.left.copy_from(q.right);
}
// CHECK-DAG: Verified: member_of [backend=z3]

int static_call()
  cppverify::post(cppverify::result == 0)
{
  return Counter::zero();
}
// CHECK-DAG: Verified: static_call [backend=z3]

// The default frame of reset is the object, which a caller must allow.
int cleared(Counter &c)
  cppverify::modifies(c)
  cppverify::post(cppverify::result == 10)
{
  c.reset();
  return c.n + c.limit;
}
// CHECK-DAG: Verified: cleared [backend=z3]

void cleared_narrow(Counter &c)
  cppverify::modifies(c.n)
{
  c.reset();
}
// CHECK-DAG: :[[@LINE-2]]:5: error: verification failed: cleared_narrow [frame]

// `this` and a mutable or read parameter are distinct objects by default.
void self_copy(Counter &c)
  cppverify::modifies(c.n)
{
  c.copy_from(c);
}
// CHECK-DAG: :[[@LINE-2]]:5: error: verification failed: self_copy [aliasing]

int self_plus(const Counter &c)
  cppverify::pre(-1000 < c.n && c.n < 1000)
  cppverify::post(cppverify::result == 2 * c.n)
{
  int r = c.plus(c);
  return r;
}
// CHECK-DAG: Verified: self_plus [backend=z3]

void self_copy_aliased(Counter &c)
  cppverify::modifies(c.n)
  cppverify::post(c.n == cppverify::old(c.n))
{
  c.copy_aliased(c);
}
// CHECK-DAG: Verified: self_copy_aliased [backend=z3]

// Not yet, each with its function's located error: virtual functions,
// members of classes with bases, destructors (and the constructors of a
// class with one), and conversion functions.
struct Shape {
  virtual int area() const
    cppverify::post(cppverify::result >= 0)
  {
    return 0;
  }
};
// CHECK-DAG: error: Shape::area: virtual functions are unsupported, since a call may run an override

struct Base {
  int b;
};

struct Derived : Base {
  int get() const
    cppverify::post(cppverify::result == b)
  {
    return b;
  }
};
// CHECK-DAG: error: Derived::get: member functions of a class with bases or virtual functions are unsupported

struct Made {
  int v;
  Made()
    cppverify::post(v == 0)
    : v(0) {}
  ~Made()
    cppverify::pre(v == 0)
  {}
  operator int() const
    cppverify::post(cppverify::result == v)
  {
    return v;
  }
};
// CHECK-DAG: error: Made::Made: constructors of a class that is not trivially copyable, whose copies or destruction run code, are not supported yet
// CHECK-DAG: error: Made::~Made: destructors are not verified yet
// CHECK-DAG: error: Made::operator int: conversion functions are unsupported
