// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

constexpr int twice(int x) { return 2 * x; }

int use_constexpr(int x)
  cppverify::pre(x >= 0 && x < 50)
  cppverify::post(cppverify::result == twice(x))
{
  return twice(x);
}

// VERIFY: Verified: use_constexpr