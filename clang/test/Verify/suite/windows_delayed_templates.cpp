// RUN: %cpp-verify %s -- -std=c++17 --target=x86_64-pc-windows-msvc -fdelayed-template-parsing -fms-compatibility 2>&1 | FileCheck %s
// RUN: %clang -std=c++17 --target=x86_64-pc-windows-msvc -fdelayed-template-parsing -fms-compatibility -fverify-contracts -fno-verify -fsyntax-only -Werror %s
//
// For Windows targets before C++20 the compiler delays parsing the body of a
// template to the end of the file, and code written for that needs it:
// `twice` calls a function declared after it. A template with clauses, and
// a spec or proof template, is parsed where it is defined, since its
// contract belongs to that definition; every other template is delayed as
// without contracts, constructs in its body included.

namespace cv = cppverify;

template <class T> int twice(T x) { return later(1) + x; }
int later(int x) { return 2 * x; }

// No clauses; its body is parsed late, with its loop contract and check.
template <class T> T sum_to(T n) {
  T s = 0;
  for (T i = 0; i < n; ++i)
    cv::invariant(0 <= i && i <= n && s == i)
    cv::decreases(n - i)
  {
    s = s + 1;
  }
  cv::check(s == n || n < 0);
  return s;
}

template <class T> cv::spec T twice_of(T x) { return 2 * x; }

template <class T> T doubled(T x)
  cv::pre(0 <= x && x < 1000)
  cv::post(cv::result == twice_of(x))
{
  return x + x;
}

template <class T> cv::proof void twice_is_even(T x)
  cv::post(twice_of(x) % 2 == 0)
{
}

template <int N> class Counter {
  int v;
public:
  cv::type_invariant(0 <= v && v <= N);
  int get() const { return v; }
  int next() const cv::pre(v < N) cv::post(cv::result == v + 1) { return v + 1; }
};

int use(int x)
  cv::pre(0 <= x && x < 100)
  cv::post(cv::result == 2 * x)
{
  int n = sum_to(x);
  cv::check(n == x);
  cv::ghost { twice_is_even(n); }
  return doubled(n);
}

int count(const Counter<5> &c)
  cv::post(0 <= cv::result && cv::result <= 5)
{
  return c.get();
}

int after(const Counter<5> &c, int limit)
  cv::pre(limit == 5)
  cv::post(cv::result <= 6)
{
  return c.get() < limit ? c.next() : 0;
}

int calls_later()
  cv::post(cv::result == 5)
{
  return twice(3);
}

// CHECK-DAG: Verified: doubled<int> [backend=z3]
// CHECK-DAG: Verified: twice_is_even<int> [backend=z3]
// CHECK-DAG: Verified: Counter<5>::next [backend=z3]
// CHECK-DAG: Verified: use [backend=z3]
// CHECK-DAG: Verified: count [backend=z3]
// CHECK-DAG: Verified: after [backend=z3]
// CHECK-DAG: Verified: calls_later [backend=z3]
// CHECK-NOT: error:
// CHECK-NOT: Unresolved
// CHECK: Summary: 7 verified in
