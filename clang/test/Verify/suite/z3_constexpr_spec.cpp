// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

constexpr int sq(int x) { return x * x; }

int use_sq(int x)
  pre(x >= 0 && x <= 100)
  post(result == x * x)
{
  return sq(x);
}

// VERIFY-DAG: spec axiom: sq
// VERIFY-DAG: Verified: use_sq