// RUN: not %cpp-verify --jobs=1 %s -- > %t 2>&1
// RUN: FileCheck %s < %t
// RUN: FileCheck %s --check-prefix=NOTE < %t
// RUN: FileCheck %s --check-prefix=SOUND < %t
//
// A class template is verified in each specialization the translation unit
// instantiates: its members' contracts are instantiated with the members
// used, and its type invariants with the class.
//
// No proof here holds only because no execution reaches its end.
// SOUND-NOT: vacuous


template <typename T>
class Box {
public:
  Box(T v)
    cppverify::pre(0 <= v && v <= 100)
    cppverify::post(value == v)
    : value(v) {}

  T get() const
    cppverify::post(cppverify::result == value)
  {
    return value;
  }

  // 2 * 100 is no signed char.
  T twice() const
    cppverify::post(cppverify::result == 2 * value)
  {
    return value + value;
  }

  void reset()
    cppverify::post(value == 0)
  {
    value = 0;
  }
  // CHECK-DAG: class_templates.cpp:[[@LINE-5]]:8: warning: Box<T>::reset: member of a class template is not verified: this translation unit instantiates it in none of the class's specializations

  T value;

  cppverify::type_invariant(0 <= value && value <= 100);
};

int boxed()
  cppverify::post(cppverify::result == 7)
{
  Box<int> b(7);
  int v = b.get();
  return v;
}
// CHECK-DAG: Verified: Box<int>::Box [backend=z3]
// CHECK-DAG: Verified: Box<int>::get [backend=z3]
// CHECK-DAG: Verified: boxed [backend=z3]

// The invariant of a Box<int> passed by reference.
int bounded(const Box<int> &b)
  cppverify::post(cppverify::result <= 100)
{
  int v = b.get();
  return v;
}
// CHECK-DAG: Verified: bounded [backend=z3]

int twice_int()
  cppverify::post(cppverify::result == 200)
{
  Box<int> b(100);
  int t = b.twice();
  return t;
}

signed char twice_char()
{
  Box<signed char> c(100);
  signed char t = c.twice();
  return t;
}
// CHECK-DAG: Verified: Box<int>::twice [backend=z3]
// CHECK-DAG: Verified: twice_int [backend=z3]
// CHECK-DAG: Verified: Box<signed char>::Box [backend=z3]
// CHECK-DAG: error: verification failed: Box<signed char>::twice [{{.*}}::postcondition@
// NOTE: error: verification failed: Box<signed char>::twice
// NOTE-NEXT: class_templates.cpp:[[@LINE-8]]:21: note: in instantiation of member function 'Box<signed char>::twice' requested here

// An out-of-line definition with a contract, explicitly instantiated.
template <typename T>
struct Pair {
  T a;
  T b;
  T larger() const;
};

template <typename T>
T Pair<T>::larger() const
  cppverify::post(cppverify::result >= a && cppverify::result >= b)
{
  return a < b ? b : a;
}

template struct Pair<long>;
// CHECK-DAG: Verified: Pair<long>::larger [backend=z3]

// A member function template of a class template.
template <typename T>
struct Acc {
  T total;

  template <typename U>
  void add(U d)
    cppverify::pre(0 <= d && d <= 10 && 0 <= total && total <= 1000)
    cppverify::modifies(total)
    cppverify::post(total == cppverify::old(total) + d)
  {
    total = total + d;
  }
};

int accumulated()
  cppverify::post(cppverify::result == 8)
{
  Acc<int> a;
  a.total = 0;
  a.add(5);
  a.add((short)3);
  return a.total;
}
// CHECK-DAG: Verified: Acc<int>::add<int> [backend=z3]
// CHECK-DAG: Verified: Acc<int>::add<short> [backend=z3]
// CHECK-DAG: Verified: accumulated [backend=z3]

// Never instantiated.
template <typename T>
struct Unused {
  T x;

  T same() const
    cppverify::post(cppverify::result == x)
  {
    return x;
  }
  // CHECK-DAG: class_templates.cpp:[[@LINE-5]]:5: warning: Unused<T>::same: member of a class template is not verified: this translation unit instantiates it in none of the class's specializations
};

// A spec template applied in a class template's invariant.
template <typename T>
cppverify::spec bool small(T v) { return 0 <= v && v <= 9; }

template <typename T>
class Digit {
public:
  Digit(T v)
    cppverify::pre(small(v))
    cppverify::post(d == v)
    : d(v) {}

  T get() const
    cppverify::post(cppverify::result == d)
  {
    return d;
  }

  T d;

  cppverify::type_invariant(small(d));
};

int digit()
  cppverify::post(0 <= cppverify::result && cppverify::result <= 9)
{
  Digit<int> x(7);
  int v = x.get();
  return v;
}
// CHECK-DAG: Verified: spec axiom: small<int>
// CHECK-DAG: Verified: Digit<int>::Digit [backend=z3]
// CHECK-DAG: Verified: Digit<int>::get [backend=z3]
// CHECK-DAG: Verified: digit [backend=z3]
