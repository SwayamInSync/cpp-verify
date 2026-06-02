// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

spec int double_spec(int x) { return 2 * x; }

int use_with_reveal(int x)
  pre(x >= 0 && x <= 20)
  post(result == double_spec(x))
{
  ghost { reveal_with_fuel(double_spec, 1); }
  return double_spec(x);
}

// VERIFY-DAG: spec axiom: double_spec
// VERIFY-DAG: Verified: use_with_reveal