// RUN: %cpp-verify --dump-ir=3,4 %s 2>&1 | FileCheck %s --check-prefix=DUMP
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

struct Pair {
  int a;
  int b;
};

int swap_post(int *x, int *y)
  cppverify::pre(x != 0 && y != 0 && x != y)
  cppverify::modifies(*x, *y)
  cppverify::post(cppverify::old(*x) == *y && cppverify::old(*y) == *x)
{
  int t = *x;
  *x = *y;
  *y = t;
  return 0;
}

int check_pair(Pair p)
  cppverify::pre(p.a >= 0 && p.a <= 1000 && p.b >= 0 && p.b <= 1000)
  cppverify::pre(cppverify::forall(i, 0, 1, i >= 0))
  cppverify::post(cppverify::result == p.a + p.b)
{
  return p.a + p.b;
}

// DUMP: vc swap_post
// DUMP: forall
// VERIFY-DAG: Verified: swap_post
// VERIFY-DAG: Verified: check_pair