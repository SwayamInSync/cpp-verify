// RUN: not %cpp-verify --jobs=1 %s -- > %t 2>&1
// RUN: FileCheck %s < %t
// RUN: FileCheck %s --check-prefix=SOUND < %t
//
// A class invariant holds at the boundary of every public member function,
// which assumes it on entry and must restore it, and every constructor must
// establish it. It is checked at every call, internal calls included, so a
// private member function may work with it broken, and no call observes it
// broken.
//
// No proof here holds only because no execution reaches its end.
// SOUND-NOT: vacuous

class Ring {
public:
  Ring()
    cppverify::post(head == 0 && count == 0)
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

  void push(int v)
    cppverify::pre(count < 8)
    cppverify::post(count == cppverify::old(count) + 1)
  {
    buf[(head + count) % 8] = v;
    count = count + 1;
  }

  int pop()
    cppverify::pre(count > 0)
    cppverify::post(count == cppverify::old(count) - 1)
  {
    int v = buf[head];
    head = (head + 1) % 8;
    count = count - 1;
    return v;
  }

  int size() const
    cppverify::post(cppverify::result == count)
  {
    return count;
  }

  int front_index() const
    cppverify::post(cppverify::result == head)
  {
    return head;
  }

  // Breaks the invariant.
  void skip()
    cppverify::post(true)
  {
    head = 8;
  }

  // Works with the invariant broken, then restores it.
  void rotate()
    cppverify::post(true)
  {
    set_head(9);
    set_head(0);
  }

  // Calls a public member function with the invariant broken.
  int peek_broken()
    cppverify::post(true)
  {
    set_head(9);
    int n = size();
    set_head(0);
    return n;
  }

private:
  void set_head(int h)
    cppverify::modifies(head)
    cppverify::post(head == h)
  {
    head = h;
  }

  int buf[8];
  int head;
  int count;

public:
  cppverify::type_invariant(0 <= head && head < 8 && 0 <= count && count <= 8);
};
// CHECK-DAG: Verified: Ring::Ring [backend=z3]
// CHECK-DAG: Verified: Ring::push [backend=z3]
// CHECK-DAG: Verified: Ring::pop [backend=z3]
// CHECK-DAG: Verified: Ring::size [backend=z3]
// CHECK-DAG: Verified: Ring::rotate [backend=z3]
// CHECK-DAG: Verified: Ring::set_head [backend=z3]
// CHECK-DAG: error: verification failed: Ring::skip [type-invariant]
// CHECK-DAG: error: verification failed: Ring::peek_broken [type-invariant]

// A constructor that does not establish the invariant.
class Window {
public:
  Window(int f)
    cppverify::post(first == f)
    : first(f) {}

  int first;

  cppverify::type_invariant(0 <= first && first < 100);
};
// CHECK-DAG: error: verification failed: Window::Window [type-invariant]

class Bounded {
public:
  Bounded(int f)
    cppverify::pre(0 <= f && f < 100)
    cppverify::post(first == f)
    : first(f) {}

  int get() const
    cppverify::post(cppverify::result == first)
  {
    return first;
  }

  int first;

  cppverify::type_invariant(0 <= first && first < 100);
};
// CHECK-DAG: Verified: Bounded::Bounded [backend=z3]

// A caller knows the invariant after construction and after every public
// call, and must establish it before every public call.
int known()
  cppverify::post(0 <= cppverify::result && cppverify::result < 100)
{
  Bounded b(42);
  int v = b.get();
  return v;
}
// CHECK-DAG: Verified: known [backend=z3]

int ring_use()
  cppverify::post(cppverify::result == 1)
{
  Ring r;
  r.push(7);
  int i = r.front_index();
  cppverify::check(0 <= i && i < 8);
  int n = r.size();
  return n;
}
// CHECK-DAG: Verified: ring_use [backend=z3]

// pop's contract does not say what it returns.
int ring_value()
  cppverify::post(cppverify::result == 7)
{
  Ring r;
  r.push(7);
  int v = r.pop();
  return v;
}
// CHECK-DAG: error: verification failed: ring_value [postcondition]

int broken_by_caller()
  cppverify::post(true)
{
  Bounded b(1);
  b.first = 500;
  return b.get();
}
// CHECK-DAG: :[[@LINE-2]]:{{[0-9]+}}: error: verification failed: broken_by_caller [type-invariant]

// An extent in a class invariant: on entry `this->data` points to `len`
// elements, as a pointer field's extent in a precondition does. At exit the
// marker states nothing; the next call checks the extent from what its
// caller knows.
class View {
public:
  View(const int *p, int n)
    cppverify::pre(cppverify::valid(p, n) && 0 <= n && n < 1000)
    cppverify::post(data == p && len == n)
    : data(p), len(n) {}

  int first() const
    cppverify::pre(len > 0)
    cppverify::post(cppverify::result == data[0])
  {
    return data[0];
  }

  void grow()
    cppverify::pre(len < 999)
    cppverify::modifies(len)
    cppverify::post(len == cppverify::old(len) + 1)
  {
    len = len + 1;
  }

  const int *data;
  int len;

  cppverify::type_invariant(cppverify::valid(data, len) && len >= 0 && len < 1000);
};
// CHECK-DAG: Verified: View::View [backend=z3]
// CHECK-DAG: Verified: View::first [backend=z3]
// CHECK-DAG: Verified: View::grow [backend=z3]

int first_of(const int *p, int n)
  cppverify::pre(cppverify::valid(p, n) && 0 < n && n < 1000)
  cppverify::post(cppverify::result == p[0])
{
  View v(p, n);
  int x = v.first();
  return x;
}
// CHECK-DAG: Verified: first_of [backend=z3]

int grown(const int *p, int n)
  cppverify::pre(cppverify::valid(p, n) && 0 < n && n < 999)
{
  View v(p, n);
  v.grow();
  int x = v.first();
  return x;
}
// CHECK-DAG: :[[@LINE-3]]:{{[0-9]+}}: error: verification failed: grown [bounds]
