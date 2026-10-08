// RUN: %cpp-verify %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY

cppverify::spec int s(int x) { return x + 1; }

int client(int x)
  cppverify::pre(x >= -100 && x < 100)
  cppverify::pre(x < 0 || s(x) > 0)
  cppverify::post(cppverify::result == s(x))
{
  return x + 1;
}

// VERIFY: Verified: client