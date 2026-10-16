// RUN: %clang_cc1 -std=c++17 -fverify-contracts -fno-verify -verify %s
// RUN: %clang_cc1 -std=c++17 -fverify-contracts -fno-verify -emit-llvm -o - %s | FileCheck %s
//
// A contract may depend on a template parameter: it is checked where it is
// instantiated, as C++ conditions are. Templates are not verified yet, so the
// contracts of a function or class template are ignored with a warning, and
// the template compiles and instantiates like any other.

template <typename T>
T clamp_low(T v, T lo) // expected-warning {{contracts in function template 'clamp_low' are not yet supported and are ignored}}
  cppverify::pre(lo <= v || v < lo)
  cppverify::post(cppverify::result >= lo)
{
  return v < lo ? lo : v;
}

template <typename T>
T sum_to(T n) // expected-warning {{contracts in function template 'sum_to' are not yet supported and are ignored}}
  cppverify::pre(n >= 0)
{
  T total = 0;
  for (T i = 0; i < n; i = i + 1) // expected-warning {{contracts in function template 'sum_to' are not yet supported and are ignored}}
    cppverify::invariant(0 <= i && i <= n)
    cppverify::decreases(n - i)
  {
    total = total + i;
  }
  return total;
}

template <typename T>
void fill(T *p, T n, T v) // expected-warning {{contracts in function template 'fill' are not yet supported and are ignored}}
  cppverify::modifies(p[0 : n])
{
  for (T i = 0; i < n; i = i + 1)
    p[i] = v;
}

template <typename T>
struct Box {
  T value;
  cppverify::type_invariant(value == value); // expected-warning {{contracts in class template 'Box' are not yet supported and are ignored}}

  T get() const
    cppverify::post(cppverify::result == value) // expected-warning {{contracts on member functions are not yet supported and are ignored}}
  {
    return value;
  }
};

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
         quantified(6);
}

// CHECK-DAG: define {{.*}} @_Z9clamp_lowIiET_S0_S0_(
// CHECK-DAG: define {{.*}} @_Z6sum_toIiET_S0_(
// CHECK-DAG: define {{.*}} @_Z6sum_toIlET_S0_(
// CHECK-DAG: define {{.*}} @_Z4fillIiEvPT_S0_S0_(
// CHECK-DAG: define {{.*}} @_ZNK3BoxIiE3getEv(
// CHECK-DAG: define {{.*}} @_Z7checkedIiET_S0_(
// CHECK-DAG: define {{.*}} @_Z10quantifiedIiET_S0_(
// CHECK-DAG: define {{.*}} @_ZZ10quantifiedIiET_S0_ENKUlS0_E_clIiEEDaS0_(
