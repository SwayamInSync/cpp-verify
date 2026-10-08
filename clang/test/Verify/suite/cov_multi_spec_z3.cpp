// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

cppverify::spec int inc_s(int x) { return x + 1; }
cppverify::spec int add_s(int x, int y) { return x + y; }

int chain(int x)
  cppverify::pre(x >= 0 && x < 100)
  cppverify::post(cppverify::result == add_s(inc_s(x), x))
{
  return 2 * x + 1;
}

// VERIFY-DAG: spec axiom: inc_s
// VERIFY-DAG: spec axiom: add_s
// VERIFY-DAG: Verified: chain