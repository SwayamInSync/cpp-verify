// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=CHECK

cppverify::spec int need_pos(int x)
  cppverify::recommends(x > 0)
{
  return x;
}

int caller(int x)
  cppverify::pre(x == 0)
  cppverify::post(cppverify::result >= 0)
{
  cppverify::ghost {
    int checked = need_pos(x);
    cppverify::check(checked > 0);
  }
  return x;
}

// CHECK: verification failed: caller