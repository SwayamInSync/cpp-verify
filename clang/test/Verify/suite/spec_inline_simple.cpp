// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY

cppverify::spec int double_spec(int x) { return 2 * x; }

int use_double(int x)
  cppverify::pre(x >= 0 && x <= 100)
  cppverify::post(cppverify::result == double_spec(x))
{
  cppverify::ghost {
    int doubled = double_spec(x);
    cppverify::check(doubled == 2 * x);
  }
  return 2 * x;
}

// VERIFY-DAG: spec axiom: double_spec
// VERIFY-DAG: Verified: use_double