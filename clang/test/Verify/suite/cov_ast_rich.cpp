// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

struct Pair {
  int a;
  int b;
};

int inc(int x)
  cppverify::pre(x >= 0 && x < 50)
  cppverify::post(cppverify::result == x + 1)
{
  return x + 1;
}

int rich(int n, int *p)
  cppverify::pre(n >= 0 && n <= 2 && p != 0)
  cppverify::modifies(*p)
  cppverify::post(cppverify::result >= 0)
{
  Pair pr;
  pr.a = 0;
  pr.b = 1;
  int t = inc(n);
  *p = 7;
  return pr.a + pr.b + t;
}

// VERIFY: Verified: rich