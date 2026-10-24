// RUN: not %cpp-verify --jobs=1 %s -- > %t 2>&1
// RUN: FileCheck %s < %t
// RUN: FileCheck %s --check-prefix=SOUND < %t
// RUN: not %cpp-verify --jobs=1 --backend=bmc --unroll=9 %s -- 2>&1 \
// RUN:   | FileCheck %s --check-prefix=BMC
//
// A constructor runs on storage its caller allocated: its object is
// uninitialized when it is entered, its member initializers run first, in
// declaration order, and it must initialize every member by its end. The
// caller passes the object's address as `this` and holds an initialized
// object after the call. An implicit or defaulted default constructor
// initializes the members as their declarations say.
//
// No proof here holds only because no execution reaches its end.
// SOUND-NOT: vacuous

struct Counter {
  Counter()
    cppverify::post(n == 0 && limit == 10)
    : n(0), limit(10) {}

  Counter(int l)
    cppverify::pre(l > 0)
    cppverify::post(n == 0 && limit == l)
  {
    n = 0;
    limit = l;
  }

  void bump()
    cppverify::pre(n < limit)
    cppverify::modifies(n)
    cppverify::post(n == cppverify::old(n) + 1)
  {
    n = n + 1;
  }

  int n;
  int limit;
};
// CHECK-DAG: Verified: Counter::Counter [backend=z3]
// BMC-DAG: Verified: Counter::Counter [backend=bmc, bound=0]

int made()
  cppverify::post(cppverify::result == 16)
{
  Counter c;
  Counter d(5);
  Counter e{1};
  d.bump();
  return c.limit + d.limit + c.n + d.n + e.n;
}
// CHECK-DAG: Verified: made [backend=z3]
// BMC-DAG: Verified: made [backend=bmc, bound=0]

// A conversion by the constructor, and a copy, which copies the members.
int converted()
  cppverify::post(cppverify::result == 6)
{
  Counter f = Counter(3);
  Counter g = f;
  return f.limit + g.limit;
}
// CHECK-DAG: Verified: converted [backend=z3]

// Construction writes only the object constructed.
int others_kept()
  cppverify::post(cppverify::result == 6)
{
  int x = 1;
  int &r = x;
  Counter c(5);
  return r + c.limit;
}
// CHECK-DAG: Verified: others_kept [backend=z3]

// Every member must be initialized.
struct Partial {
  Partial(int l)
    cppverify::post(limit == l)
  {
    limit = l;
  }

  int n;
  int limit;
};
// CHECK-DAG: error: verification failed: Partial::Partial [{{.*}}::initialization@[[@LINE-3]]:7]

// Members are initialized in declaration order, whatever the order of the
// initializers: `n` reads `limit` before it is initialized.
struct Early {
  Early()
    cppverify::post(true)
    : limit(0), n(limit) {}

  int n;
  int limit;
};
// CHECK-DAG: error: verification failed: Early::Early [{{.*}}::initialization@

// The in-class initializers of the members a constructor does not name run
// in their place.
struct Defaults {
  Defaults()
    cppverify::post(a == 1 && b == 2)
    : b(2) {}

  int a = 1;
  int b;
};
// CHECK-DAG: Verified: Defaults::Defaults [backend=z3]

// An implicit default constructor is its members' initializers.
struct Point {
  int x = 3;
  int y = 4;
};

int point_sum()
  cppverify::post(cppverify::result == 7)
{
  Point p;
  return p.x + p.y;
}
// CHECK-DAG: Verified: point_sum [backend=z3]

// So is one whose member's class has an implicit one.
struct Holder {
  Point p;
  int z = 0;
};

int holder_sum()
  cppverify::post(cppverify::result == 7)
{
  Holder h;
  return h.p.x + h.p.y + h.z;
}
// CHECK-DAG: Verified: holder_sum [backend=z3]

// A member function called on the object before every member is
// initialized reads it as initialized, which C++ does not require: such a
// call is construct.unsupported, as an out-parameter's is.
struct Resets {
  Resets()
    cppverify::post(v == 0)
  {
    reset();
  }

  void reset()
    cppverify::modifies(v)
    cppverify::post(v == 0)
  {
    v = 0;
  }

  int v;
};
// CHECK-DAG: Unresolved: Resets::Resets [backend=z3] [reason=construct.unsupported]

// A loop initializes an array member, as an invariant states.
struct Ring {
  Ring()
    cppverify::post(head == 0 && count == 0)
    cppverify::post(cppverify::forall(k, 0, 8, buf[k] == 0))
    : head(0), count(0)
  {
    for (int i = 0; i < 8; i = i + 1)
      cppverify::invariant(0 <= i && i <= 8)
      cppverify::invariant(head == 0 && count == 0)
      cppverify::invariant(cppverify::forall(k, 0, i, buf[k] == 0))
      cppverify::decreases(8 - i)
    {
      buf[i] = 0;
    }
  }

  int buf[8];
  int head;
  int count;
};
// CHECK-DAG: Verified: Ring::Ring [backend=z3]

// A loop writes only the object constructed: the source keeps its values.
struct Copy4 {
  Copy4(const int *src)
    cppverify::pre(cppverify::valid(src, 4))
    cppverify::post(cppverify::forall(k, 0, 4, buf[k] == cppverify::old(src[k])))
  {
    for (int i = 0; i < 4; i = i + 1)
      cppverify::invariant(0 <= i && i <= 4)
      cppverify::invariant(cppverify::forall(k, 0, i, buf[k] == src[k]))
      cppverify::decreases(4 - i)
    {
      buf[i] = src[i];
    }
  }

  int buf[4];
};
// CHECK-DAG: Verified: Copy4::Copy4 [backend=z3]

int ring_count()
  cppverify::post(cppverify::result == 0)
{
  Ring r;
  return r.count + r.buf[7];
}
// CHECK-DAG: Verified: ring_count [backend=z3]

// A constructor that writes another object states it.
struct Logged {
  Logged(int *log)
    cppverify::pre(log != nullptr)
    cppverify::modifies(*log)
    cppverify::post(v == 1 && *log == 1)
  {
    v = 1;
    *log = 1;
  }

  int v;
};
// CHECK-DAG: Verified: Logged::Logged [backend=z3]

int logged()
  cppverify::post(cppverify::result == 2)
{
  int log = 0;
  Logged l(&log);
  return log + l.v;
}
// CHECK-DAG: Verified: logged [backend=z3]

// Not supported, each with its function's located error.
struct Reads {
  Reads()
    cppverify::pre(v == 0)
    : v(0) {}

  int v;
};
// CHECK-DAG: error: Reads::Reads: a constructor's precondition cannot read its object, whose lifetime has not begun

struct Delegates {
  Delegates(int v)
    cppverify::post(w == v)
    : w(v) {}
  Delegates()
    cppverify::post(w == 0)
    : Delegates(0) {}

  int w;
};
// CHECK-DAG: error: Delegates::Delegates: delegating constructors are not verified yet

struct Unverified {
  Unverified() : v(0) {}
  int v;
};

int uses_unverified()
  cppverify::post(cppverify::result == 0)
{
  Unverified u;
  return u.v;
}
// CHECK-DAG: error: uses_unverified: call to function without a verification contract: Unverified::Unverified
