// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int pick_first(int n)
  cppverify::pre(n > 0 && n <= 5)
  cppverify::pre(cppverify::forall(i, 0, n, i >= 0))
  cppverify::post(cppverify::result >= 0)
{
  return 0;
}

// VERIFY: Verified: pick_first