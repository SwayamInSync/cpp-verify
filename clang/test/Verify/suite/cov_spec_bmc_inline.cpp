// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --backend=bmc --unroll=2 %s 2>&1 | FileCheck %s --check-prefix=VERIFY

cppverify::spec int inc_spec(int x) { return x + 1; }

int use_spec(int x)
  cppverify::pre(x >= 0 && x < 20)
  cppverify::post(cppverify::result == inc_spec(x))
{
  return x + 1;
}

// VERIFY: Verified: use_spec