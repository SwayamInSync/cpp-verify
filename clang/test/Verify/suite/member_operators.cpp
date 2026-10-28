// RUN: not %cpp-verify --jobs=1 %s -- > %t 2>&1
// RUN: FileCheck %s < %t
// RUN: FileCheck %s --check-prefix=SOUND < %t
//
// A member operator is a member function: `a == b` is `a.operator==(b)`,
// whose object is its first operand. One that returns a reference to its
// own object (`return *this;`) returns nothing a caller does not hold.
//
// No proof here holds only because no execution reaches its end.
// SOUND-NOT: vacuous

class Bits {
public:
  Bits()
    cppverify::post(word == 0)
    : word(0) {}

  void set(int i)
    cppverify::pre(0 <= i && i < 16)
    cppverify::modifies(word)
    cppverify::post(word == (cppverify::old(word) | (1u << i)))
  {
    word = word | (1u << i);
  }

  bool test(int i) const
    cppverify::pre(0 <= i && i < 16)
    cppverify::post(cppverify::result == (((word >> i) & 1u) != 0))
  {
    return ((word >> i) & 1u) != 0;
  }

  bool operator==(const Bits &o) const
    cppverify::post(cppverify::result == (word == o.word))
  {
    return word == o.word;
  }

  Bits &operator|=(const Bits &o)
    cppverify::modifies(word)
    cppverify::post(word == (cppverify::old(word) | o.word))
  {
    word = word | o.word;
    return *this;
  }

  unsigned word;

  cppverify::type_invariant(word < 65536);
};
// CHECK-DAG: Verified: Bits::Bits [backend=z3]
// CHECK-DAG: Verified: Bits::set [backend=z3]
// CHECK-DAG: Verified: Bits::test [backend=z3]
// CHECK-DAG: Verified: Bits::operator== [backend=z3]
// CHECK-DAG: Verified: Bits::operator|= [backend=z3]

int bits_use()
  cppverify::post(cppverify::result == 1)
{
  Bits a;
  Bits b;
  a.set(3);
  b.set(5);
  bool apart = a == b;
  a |= b;
  b |= a;
  bool together = a == b;
  bool has = a.test(5);
  return (!apart && together && has) ? 1 : 0;
}
// CHECK-DAG: Verified: bits_use [backend=z3]

struct Money {
  Money(int c)
    cppverify::pre(0 <= c && c < 1000000)
    cppverify::post(cents == c)
    : cents(c) {}

  Money &operator+=(const Money &o)
    cppverify::pre(0 <= o.cents && o.cents < 1000000)
    cppverify::pre(0 <= cents && cents < 1000000)
    cppverify::modifies(cents)
    cppverify::post(cents == cppverify::old(cents) + o.cents)
  {
    cents = cents + o.cents;
    return *this;
  }

  int cents;
};

// A free operator is a free function, and returns its value.
Money operator+(const Money &a, const Money &b)
  cppverify::pre(0 <= a.cents && a.cents < 500000)
  cppverify::pre(0 <= b.cents && b.cents < 500000)
  cppverify::post(cppverify::result.cents == a.cents + b.cents)
{
  Money r(a.cents + b.cents);
  return r;
}
// CHECK-DAG: Verified: operator+ [backend=z3]

int summed()
  cppverify::post(cppverify::result == 22)
{
  Money a(5);
  Money b(6);
  Money c = a + b;
  a += b;
  return c.cents + a.cents;
}
// CHECK-DAG: Verified: summed [backend=z3]

// The object and the operand are distinct objects by default.
int self_add()
  cppverify::post(true)
{
  Money a(5);
  a += a;
  return a.cents;
}
// CHECK-DAG: :[[@LINE-3]]:{{[0-9]+}}: error: verification failed: self_add [aliasing]

// The reference such an operator returns is no value yet.
int chained()
  cppverify::post(true)
{
  Money a(5);
  Money b(6);
  (a += b) += b;
  return a.cents;
}
// CHECK-DAG: error: chained: the reference operator+= returns is not used yet; call it as a statement of its own

int copied()
  cppverify::post(true)
{
  Money a(5);
  Money b(6);
  Money c = (a += b);
  return c.cents;
}
// CHECK-DAG: error: copied: the reference operator+= returns is not used yet; call it as a statement of its own

int assigned()
  cppverify::post(true)
{
  Money a(5);
  Money b(6);
  Money c(0);
  c = (a += b);
  return c.cents;
}
// CHECK-DAG: error: assigned: the reference operator+= returns is not used yet; call it as a statement of its own

// An object a parameter refers to or points to satisfies its class
// invariant on entry, as the caller shows, and through a mutable reference
// or pointer it must at exit: so does every operand of an operator.
class Level {
public:
  Level(int v)
    cppverify::pre(0 <= v && v < 100)
    cppverify::post(value == v)
    : value(v) {}

  int get() const
    cppverify::post(cppverify::result == value)
  {
    return value;
  }

  int value;

  cppverify::type_invariant(0 <= value && value < 100);
};
// CHECK-DAG: Verified: Level::Level [backend=z3]

int read(const Level &l)
  cppverify::post(0 <= cppverify::result && cppverify::result < 100)
{
  int v = l.get();
  return v;
}
// CHECK-DAG: Verified: read [backend=z3]

int peek(const Level *p)
  cppverify::post(p == nullptr || cppverify::result < 100)
{
  if (p == nullptr)
    return 0;
  int v = p->get();
  return v;
}
// CHECK-DAG: Verified: peek [backend=z3]

void lower(Level &l)
  cppverify::modifies(l.value)
{
  l.value = l.value / 2;
}
// CHECK-DAG: Verified: lower [backend=z3]

void spoil(Level &l)
  cppverify::modifies(l.value)
{
  l.value = 500;
}
// CHECK-DAG: error: verification failed: spoil [type-invariant]

int spoiled_argument()
  cppverify::post(true)
{
  Level l(1);
  l.value = 500;
  int v = read(l);
  return v;
}
// CHECK-DAG: :[[@LINE-3]]:{{[0-9]+}}: error: verification failed: spoiled_argument [type-invariant]

// A null pointer addresses no object, whose invariant would be due.
int none()
  cppverify::post(true)
{
  int v = peek(nullptr);
  return v;
}
// CHECK-DAG: Verified: none [backend=z3]

// An extent in a class invariant is `this`'s: an object passed by
// reference does not carry it yet, so a member function that needs it
// cannot be called there.
class Span {
public:
  Span(const int *p, int n)
    cppverify::pre(cppverify::valid(p, n) && 0 < n && n < 1000)
    cppverify::post(data == p && len == n)
    : data(p), len(n) {}

  int first() const
    cppverify::post(cppverify::result == data[0])
  {
    return data[0];
  }

  const int *data;
  int len;

  cppverify::type_invariant(cppverify::valid(data, len) && 0 < len && len < 1000);
};

int first_through(const Span &s)
  cppverify::post(true)
{
  int v = s.first();
  return v;
}
// CHECK-DAG: :[[@LINE-3]]:{{[0-9]+}}: error: verification failed: first_through [bounds]
