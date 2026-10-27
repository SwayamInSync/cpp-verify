// RUN: %clang_cc1 -std=c++17 -fverify-contracts -fno-verify -verify %s
// RUN: %clang_cc1 -std=c++17 -fverify-contracts -fno-verify -emit-llvm -o - %s | FileCheck %s
// RUN: %clang_cc1 -std=c++17 -fverify-contracts -fno-verify -ast-dump -ast-dump-filter temporaries %s | FileCheck %s --check-prefix=CLEANUPS
// expected-no-diagnostics
//
// A contract may depend on a template parameter: it is checked where it is
// instantiated, as C++ conditions are. A function template's contract is
// instantiated with each specialization, and a class template's members'
// contracts and type invariants with the class. Either compiles and
// instantiates like any other template.

template <typename T>
T clamp_low(T v, T lo)
  cppverify::pre(lo <= v || v < lo)
  cppverify::post(cppverify::result >= lo)
{
  return v < lo ? lo : v;
}

template <typename T>
T sum_to(T n)
  cppverify::pre(n >= 0)
{
  T total = 0;
  for (T i = 0; i < n; i = i + 1)
    cppverify::invariant(0 <= i && i <= n)
    cppverify::decreases(n - i)
  {
    total = total + i;
  }
  return total;
}

template <typename T>
void fill(T *p, T n, T v)
  cppverify::modifies(p[0 : n])
{
  for (T i = 0; i < n; i = i + 1)
    p[i] = v;
}

template <typename T>
struct Box {
  T value;
  cppverify::type_invariant(value == value);

  T get() const
    cppverify::post(cppverify::result == value)
  {
    return value;
  }
};

template <typename T>
T positive(T v)
  cppverify::pre(v > 0)
  cppverify::post(cppverify::result > 0)
  cppverify::post(cppverify::old(v) > 0 && cppverify::result == v)
{
  return v;
}

// A contract instantiated while a caller's full expression is built leaves
// the caller its temporaries, whose destructors run at its end: an argument
// passed by value is one before the call is resolved.
struct Noisy {
  int v;
  Noisy(int x) : v(x) {}
  ~Noisy();
};

template <typename T>
int value_of(T t)
  cppverify::post(cppverify::result == t.v)
{
  return t.v;
}

int temporaries() { return value_of(Noisy(3)); }
// CLEANUPS-LABEL: FunctionDecl {{.*}} temporaries 'int ()'
// CLEANUPS: ReturnStmt
// CLEANUPS-NEXT: ExprWithCleanups

template <typename T>
T checked(T n)
{
  cppverify::check(cppverify::forall(k, 0, 3, k >= 0 && n == n));
  return n;
}

template <typename T>
T quantified(T n)
{
  cppverify::check(cppverify::exists(k, 0, 3, k == n - n));
  cppverify::check(cppverify::forall(i, 0, 2, cppverify::exists(j, 0, 3, j == i + (n - n))));
  cppverify::check(cppverify::forall(k, 0, 3, k + n >= n)) by {
    cppverify::check(k >= 0);
  }
  cppverify::ghost {
    int c = cppverify::choose(k, 0, 3, k == n - n);
  }
  auto twice = [](auto m) {
    cppverify::check(cppverify::forall(k, 0, 2, k < m + 2));
    return m + m;
  };
  return twice(n);
}

int use() {
  int buffer[2];
  fill(buffer, 2, 7);
  Box<int> b{3};
  return clamp_low(1, 2) + b.get() + sum_to(4) + sum_to(4L) + checked(5) +
         quantified(6) + positive(7);
}

// CHECK-DAG: define {{.*}} @_Z9clamp_lowIiET_S0_S0_(
// CHECK-DAG: define {{.*}} @_Z6sum_toIiET_S0_(
// CHECK-DAG: define {{.*}} @_Z6sum_toIlET_S0_(
// CHECK-DAG: define {{.*}} @_Z4fillIiEvPT_S0_S0_(
// CHECK-DAG: define {{.*}} @_ZNK3BoxIiE3getEv(
// CHECK-DAG: define {{.*}} @_Z8positiveIiET_S0_(
// CHECK-DAG: define {{.*}} @_Z7checkedIiET_S0_(
// CHECK-DAG: define {{.*}} @_Z10quantifiedIiET_S0_(
// CHECK-DAG: define {{.*}} @_ZZ10quantifiedIiET_S0_ENKUlS0_E_clIiEEDaS0_(
