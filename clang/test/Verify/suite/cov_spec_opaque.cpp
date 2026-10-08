// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

cppverify::spec int hidden(int x) { return x + 1; }

int client(int x)
  cppverify::pre(x >= 0 && x < 10)
  cppverify::post(cppverify::result == x)
{
  cppverify::ghost { cppverify::hide(hidden); }
  return x;
}

cppverify::spec int rec(int n)
  cppverify::decreases(n)
{
  if (n <= 0)
    return 0;
  return rec(n - 1) + 1;
}

int use_rec(int n)
  cppverify::pre(n >= 0 && n <= 1)
  cppverify::post(cppverify::result == rec(n))
  cppverify::decreases(n)
{
  cppverify::ghost { cppverify::reveal_with_fuel(rec, 2); }
  return n;
}

// VERIFY-DAG: Verified: client
// VERIFY-DAG: Verified: use_rec