// RUN: not %cpp-verify --jobs=1 %s -- > %t 2>&1
// RUN: FileCheck %s < %t
// RUN: FileCheck %s --check-prefix=SOUND < %t
// RUN: not %cpp-verify --jobs=1 --backend=bmc %s -- 2>&1 \
// RUN:   | FileCheck %s --check-prefix=BMC
//
// A record kept in memory, a local object or one a pointer or reference
// addresses, is passed and returned by value as its fields, each read where
// it is, with the checks of that read: in bounds, valid, and initialized.
//
// No proof here holds only because no execution reaches its end.
// SOUND-NOT: vacuous

struct Counter {
  Counter(int l)
    cppverify::post(n == 0 && limit == l)
    : n(0), limit(l) {}

  int n;
  int limit;
};

int limit_of(Counter c)
  cppverify::post(cppverify::result == c.limit)
{
  return c.limit;
}

// A constructed object, which is kept in memory, passed by value.
int passed()
  cppverify::post(cppverify::result == 6)
{
  Counter c(6);
  return limit_of(c);
}
// CHECK-DAG: Verified: passed [backend=z3]
// BMC-DAG: Verified: passed [backend=bmc, bound=0]

// And returned by value.
Counter make(int l)
  cppverify::post(cppverify::result.n == 0 && cppverify::result.limit == l)
{
  Counter c(l);
  return c;
}
// CHECK-DAG: Verified: make [backend=z3]

int made()
  cppverify::post(cppverify::result == 9)
{
  Counter m = make(9);
  return m.limit + m.n;
}
// CHECK-DAG: Verified: made [backend=z3]

// A record through a pointer or a reference, by value.
int through_pointer(const Counter *p)
  cppverify::pre(p != nullptr)
  cppverify::post(cppverify::result == p->limit)
{
  return limit_of(*p);
}
// CHECK-DAG: Verified: through_pointer [backend=z3]

int copied_through(const Counter *p)
  cppverify::pre(p != nullptr)
  cppverify::post(cppverify::result == p->n)
{
  Counter copy = *p;
  return copy.n;
}
// CHECK-DAG: Verified: copied_through [backend=z3]

int through_reference(const Counter &c)
  cppverify::post(cppverify::result == c.limit)
{
  return limit_of(c);
}
// CHECK-DAG: Verified: through_reference [backend=z3]

Counter returned_through(const Counter &c)
  cppverify::post(cppverify::result.limit == c.limit)
{
  return c;
}
// CHECK-DAG: Verified: returned_through [backend=z3]

// A whole record through a pointer, returned, and given to a spec.
Counter returned_pointee(const Counter *p)
  cppverify::pre(p != nullptr)
  cppverify::post(cppverify::result.n == p->n)
{
  return *p;
}
// CHECK-DAG: Verified: returned_pointee [backend=z3]

cppverify::spec int spare(Counter c) { return c.limit - c.n; }

int spare_of(const Counter *p)
  cppverify::pre(p != nullptr && 0 <= p->n && p->n <= p->limit)
  cppverify::post(cppverify::result == spare(*p))
{
  return p->limit - p->n;
}
// CHECK-DAG: Verified: spare_of [backend=z3]

// An element of an array member, read where it is: its index is checked
// against the array, though `items[2]` would be `count` and `spare`, inside
// the object.
struct Bag {
  Counter items[2];
  int count;
  int spare;
};

int element(const Bag *b, int k)
  cppverify::pre(b != nullptr && 0 <= k && k < 2)
  cppverify::post(cppverify::result == b->items[k].limit)
{
  return limit_of(b->items[k]);
}
// CHECK-DAG: Verified: element [backend=z3]

int past_element(const Bag *b, int k)
  cppverify::pre(b != nullptr && 0 <= k && k <= 2)
{
  return limit_of(b->items[k]);
}
// CHECK-DAG: :[[@LINE-2]]:{{[0-9]+}}: error: verification failed: past_element [bounds]

// A copy reads every field, so each must be initialized.
struct Pair {
  int a;
  int b;
};

int pair_sum(Pair p)
  cppverify::pre(-1000 < p.a && p.a < 1000 && -1000 < p.b && p.b < 1000)
  cppverify::post(cppverify::result == p.a + p.b)
{
  return p.a + p.b;
}

int half_initialized()
  cppverify::post(true)
{
  Pair p;
  int &a = p.a;
  a = 1;
  return pair_sum(p);
}
// CHECK-DAG: :[[@LINE-2]]:{{[0-9]+}}: error: verification failed: half_initialized [initialization]
