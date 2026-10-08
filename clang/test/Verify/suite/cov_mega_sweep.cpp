// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: %cpp-verify --backend=bmc --unroll=2 %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: %cpp-verify --backend=lean --lean-out=%t.lean %s > %t.lean.out 2>&1
// RUN: FileCheck %s --check-prefix=LEAN < %t.lean.out
// RUN: not grep -q '^Verified:' %t.lean.out

cppverify::spec int inc(int x) { return x + 1; }

cppverify::spec int pick(int x)
{
  if (x < 0)
    return 0;
  return x;
}

cppverify::spec int rec(int n)
  cppverify::decreases(n)
{
  if (n <= 0)
    return 0;
  return rec(n - 1) + 1;
}

int exec_client(int x)
  cppverify::pre(x >= 0 && x < 20)
  cppverify::post(cppverify::result == inc(inc(x)))
  cppverify::recommends(pick(x) >= 0)
{
  cppverify::ghost {
    cppverify::reveal(inc);
    cppverify::check(x >= 0);
    int twice = inc(inc(x));
    cppverify::check(twice == x + 2);
  }
  return x + 2;
}

int loop_client(int n, int *p)
  cppverify::pre(n >= 0 && n <= 1 && p != 0)
  cppverify::pre(cppverify::forall(i, 0, n, i >= 0))
  cppverify::modifies(*p)
  cppverify::post(cppverify::result >= 0)
  cppverify::decreases(n)
{
  int i = 0;
  int s = 0;
  while (i < n)
    cppverify::invariant(i >= 0 && i <= n && s == i)
    cppverify::decreases(n - i)
  {
    if (i == 0)
      s = s + 1;
    *p = s;
    i = i + 1;
  }
  return s;
}

// VERIFY-DAG: Verified: exec_client
// VERIFY-DAG: Verified: loop_client

// LEAN: Exported: lean obligation: exec_client