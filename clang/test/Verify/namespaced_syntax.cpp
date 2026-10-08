// RUN: %clang_cc1 -std=c++20 -fverify-contracts -fsyntax-only -verify %s
// expected-no-diagnostics
//
// Every construct is written qualified by the namespace cppverify: directly,
// from the global namespace, or through an alias, including one in another
// namespace or function and one written by a macro. No word is reserved, and
// <cppverify.h> needs no #include.

namespace cv = cppverify;
namespace lib {
namespace v = ::cppverify;
}
#define PRE(c) cv::pre(c)

struct Account {
  int balance;
  cv::type_invariant(balance >= 0);
};

cppverify::spec int total(const int *a, int n)
  cppverify::reads(a, n)
  cppverify::decreases(n) by { cv::check(n >= n - 1); }
{
  return n <= 0 ? 0 : total(a, n - 1) + a[n - 1];
}

cv::spec bool even(int n) cv::inductive { return n == 0 || even(n - 2); }

cv::proof void even_nonnegative(int n)
  cv::pre(even(n))
  cv::post(n >= 0)
  cv::post(n % 2 == 0)
{
}

int declared(int x) cv::pre(x > 0) cv::post(cv::result > 0);
int declared(int x) { return x; }

int nested(int x)
  lib::v::pre(x > 0)
  PRE(x < 100)
  ::cppverify::post(::cppverify::result == x)
{
  return x;
}

auto trailing(int x) -> int cv::pre(x > 0) { return x; }
int with_noexcept(int x) noexcept cv::pre(x > 0) { return x; }

int loops(const int *a, int n)
  cv::pre(n >= 0 && cv::valid(a, n))
{
  int s = 0;
  for (int i = 0; i < n; ++i)
    cv::invariant(0 <= i && i <= n)
    cv::decreases(n - i)
  {
    s = s + 0;
  }
  int j = 0;
  while (j < n) cv::invariant(j <= n) cv::decreases(n - j) { ++j; }
  do {
  } while (false) cv::invariant(true) cv::decreases(0);
  return s;
}

void statements(int x) cv::pre(x > 0) {
  namespace w = cppverify;
  w::check(x > 0);
  cv::check(x >= 1) by { cv::check(x > 0); }
  cv::ghost {
    cv::reveal_with_fuel(total, 2);
    cv::hide(total);
    cv::reveal(total);
  }
  cv::ghost int g = x;
  cv::check(g == x);
  cv::calc {
    x + x;
    == { }
    2 * x;
  }
  cv::check(!(cv::exists(k, 0, x, k < 0)));
  cv::check((cv::forall(k, 0, x, k >= 0)));
}

int quantified(int n)
  cv::post(cv::forall(k, 0, cv::result, k < n || k >= n))
  cv::post(cv::old(n) == n)
{
  return n;
}

cv::spec int pick(int n) {
  return cv::choose(k, 0, 10, k * k == n && cv::trigger(k) >= 0);
}

int clamp(int x)
  cv::behavior(low, x < 0)
  cv::post(cv::result == 0)
  cv::behavior(high, x >= 0)
  cv::post(cv::result == x)
  cv::complete_behaviors
  cv::disjoint_behaviors
{
  return x < 0 ? 0 : x;
}

cv::spec bool ghostly(cppverify::seq s) { return s.len() >= 0; }

// The words are ordinary names.
struct Fields {
  int pre, post, ghost, spec, proof, result, old, invariant, check, forall;
};
int check(int result) {
  int old = result;
  return old;
}
namespace mine {
int forall = 1;
bool exists(int) noexcept { return true; }
} // namespace mine
int use_mine() { return mine::forall + mine::exists(0); }
