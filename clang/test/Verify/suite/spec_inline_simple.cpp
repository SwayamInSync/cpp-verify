// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

spec int double_spec(int x) { return 2 * x; }

int use_double(int x)
  pre(x >= 0 && x <= 100)
  post(result == double_spec(x))
{
  return double_spec(x);
}

// VERIFY-DAG: spec axiom: double_spec
// VERIFY-DAG: verified: use_double