#include <cppverify.h>
using cppverify::valid;

cppverify::spec int climb(int n) cppverify::decreases(-n) { return n >= 0 ? 0 : climb(n + 1) + 1; }

cppverify::spec int diverge(int n) cppverify::decreases(n) { return n <= 0 ? 0 : diverge(n + 1); }

cppverify::proof void climb_zero() cppverify::post(climb(0) == 0) {}

cppverify::proof void diverge_zero() cppverify::post(diverge(0) == 0) {}

int off_by_one(int x)
  cppverify::pre(x >= 0 && x <= 100)
  cppverify::post(cppverify::result == x + 1)
{
  return x + 2;
}

int relies_on_off_by_one(int x)
  cppverify::pre(x >= 0 && x <= 50)
  cppverify::post(cppverify::result == x + 1)
{
  return off_by_one(x);
}

int positive_identity(int x)
  cppverify::pre(x > 0)
  cppverify::post(cppverify::result == x)
{
  return x;
}

int unchecked_caller(int x) { return positive_identity(x); }

int sum_to(int n)
  cppverify::pre(n >= 0 && n <= 1000)
  cppverify::post(cppverify::result == n * (n + 1) / 2)
{
  int s = 0;
  for (int i = 1; i <= n; i = i + 1)
    cppverify::invariant(1 <= i && i <= n + 1 && s == (i - 1) * i / 2)
    cppverify::decreases(n + 1 - i)
  {
    s = s + i;
  }
  return s;
}

void clear(int *a, int n)
  cppverify::pre(valid(a, n) && n >= 0 && n <= 1000)
  cppverify::modifies(*a)
  cppverify::post(cppverify::forall(k, 0, n, a[k] == 0))
{
  for (int i = 0; i < n; i = i + 1)
    cppverify::invariant(0 <= i && i <= n && cppverify::forall(k, 0, i, a[k] == 0))
    cppverify::decreases(n - i)
  {
    a[i] = 0;
  }
}

int overflow(int x)
  cppverify::pre(x >= 0)
{
  return x + 1;
}

int two_failures(int x)
  cppverify::pre(x >= 0 && x <= 10)
  cppverify::post(cppverify::result == x)
{
  cppverify::check(x < 5);
  cppverify::check(x != 7);
  return x;
}

int both_ways(int x, bool up)
  cppverify::pre(x > -1000 && x < 1000)
  cppverify::post(up ? cppverify::result == x + 1 : cppverify::result == x - 1)
{
  if (up)
    return x + 1;
  return x - 1;
}
