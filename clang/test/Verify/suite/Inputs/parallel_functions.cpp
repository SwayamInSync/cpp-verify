#include <cppverify.h>
using cppverify::valid;

spec int climb(int n) decreases(-n) { return n >= 0 ? 0 : climb(n + 1) + 1; }

spec int diverge(int n) decreases(n) { return n <= 0 ? 0 : diverge(n + 1); }

proof void climb_zero() post(climb(0) == 0) {}

proof void diverge_zero() post(diverge(0) == 0) {}

int off_by_one(int x)
  pre(x >= 0 && x <= 100)
  post(result == x + 1)
{
  return x + 2;
}

int relies_on_off_by_one(int x)
  pre(x >= 0 && x <= 50)
  post(result == x + 1)
{
  return off_by_one(x);
}

int positive_identity(int x)
  pre(x > 0)
  post(result == x)
{
  return x;
}

int unchecked_caller(int x) { return positive_identity(x); }

int sum_to(int n)
  pre(n >= 0 && n <= 1000)
  post(result == n * (n + 1) / 2)
{
  int s = 0;
  for (int i = 1; i <= n; i = i + 1)
    invariant(1 <= i && i <= n + 1 && s == (i - 1) * i / 2)
    decreases(n + 1 - i)
  {
    s = s + i;
  }
  return s;
}

void clear(int *a, int n)
  pre(valid(a, n) && n >= 0 && n <= 1000)
  modifies(*a)
  post(forall(k, 0, n, a[k] == 0))
{
  for (int i = 0; i < n; i = i + 1)
    invariant(0 <= i && i <= n && forall(k, 0, i, a[k] == 0))
    decreases(n - i)
  {
    a[i] = 0;
  }
}

int overflow(int x)
  pre(x >= 0)
{
  return x + 1;
}

int two_failures(int x)
  pre(x >= 0 && x <= 10)
  post(result == x)
{
  contract_assert(x < 5);
  contract_assert(x != 7);
  return x;
}

int both_ways(int x, bool up)
  pre(x > -1000 && x < 1000)
  post(up ? result == x + 1 : result == x - 1)
{
  if (up)
    return x + 1;
  return x - 1;
}
