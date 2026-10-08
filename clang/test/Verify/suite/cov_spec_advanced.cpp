// RUN: %cpp-verify %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY

cppverify::spec int branch(int x)
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

cppverify::spec int hidden_body(int x) { return x + 1; }

int use_branch(int x)
  cppverify::pre(x >= -2 && x <= 2)
  cppverify::post(cppverify::result == branch(x))
{
  cppverify::ghost {
    int clamped = branch(x);
    cppverify::check(clamped >= 0);
  }
  if (x < 0)
    return 0;
  return x;
}

int use_rec(int n)
  cppverify::pre(n >= 0 && n <= 2)
  cppverify::post(cppverify::result == rec(n))
  cppverify::decreases(n)
{
  cppverify::ghost { cppverify::reveal_with_fuel(rec, 3); }
  return n;
}

// VERIFY-DAG: Verified: use_branch
// VERIFY-DAG: Verified: use_rec