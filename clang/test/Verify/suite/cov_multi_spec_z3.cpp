// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

spec int inc_s(int x) { return x + 1; }
spec int add_s(int x, int y) { return x + y; }

int chain(int x)
  pre(x >= 0 && x < 100)
  post(result == add_s(inc_s(x), x))
{
  return add_s(inc_s(x), x);
}

// VERIFY-DAG: spec axiom: inc_s
// VERIFY-DAG: spec axiom: add_s
// VERIFY-DAG: verified: chain