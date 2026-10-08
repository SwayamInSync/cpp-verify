// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

cppverify::spec int hidden(int x) { return x + 1; }

int client(int x)
  cppverify::pre(hidden(x) >= 0 && x >= 0 && x < 10)
  cppverify::post(cppverify::result >= 0)
{
  cppverify::ghost { cppverify::hide(hidden); }
  return x;
}

// VERIFY: Verified: client