// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

spec int double_it(int x) { return 2 * x; }

proof void lemma_double(int x)
  pre(x >= 0 && x <= 1000)
  post(double_it(x) == 2 * x)
{
}

spec int add_three(int x) { return x + 3; }

int use_specs(int x)
  pre(x >= 0 && x <= 100)
  post(result == 2 * x + 3)
{
  return add_three(double_it(x));
}

// VERIFY-DAG: spec axiom: double_it
// VERIFY-DAG: Verified: lemma_double
// VERIFY-DAG: spec axiom: add_three
// VERIFY-DAG: Verified: use_specs