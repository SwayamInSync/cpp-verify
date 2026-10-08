// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

cppverify::spec int bump(int x) { return x + 1; }

int use_bump(int x)
  cppverify::pre(x >= 0 && x < 10)
  cppverify::post(cppverify::result == x + 1)
{
  cppverify::ghost {
    cppverify::reveal(bump);
    int bumped = bump(x);
    cppverify::check(bumped == x + 1);
  }
  return x + 1;
}

// VERIFY: Verified: use_bump