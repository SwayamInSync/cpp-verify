// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

struct Pair {
  int a;
  int b;
};

int inc(int x)
  pre(x >= 0 && x < 50)
  post(result == x + 1)
{
  return x + 1;
}

int rich(int n, int *p)
  pre(n >= 0 && n <= 2)
  modifies(*p)
  post(result >= 0)
{
  Pair pr;
  pr.a = 0;
  pr.b = 1;
  int t = inc(n);
  *p = 7;
  return pr.a + pr.b + t;
}

// VERIFY: Verified: rich