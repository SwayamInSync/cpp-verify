// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

constexpr int double_it(int x) {
  return x * 2;
}

int use_constexpr_spec(int x)
  pre(x >= 0 && x <= 100)
  post(result == double_it(x))
{
  return x + x;
}

// VERIFY-DAG: constexpr spec axiom: double_it
// VERIFY-DAG: Verified: use_constexpr_spec