// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

constexpr spec int sq(int x) { return x * x; }

int use_sq(int x)
  pre(x >= 0 && x <= 100)
  post(result == x * x)
{
  return sq(x);
}

// VERIFY-DAG: constexpr spec axiom: sq
// VERIFY-DAG: verified: use_sq