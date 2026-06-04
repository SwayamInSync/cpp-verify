// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Tier-1: a returned struct that satisfies its type_invariant verifies.
struct Box {
  int w;
  int h;
  type_invariant(w >= 0 && h >= 0);
};

Box make_box(int a, int b)
  pre(a >= 0 && a <= 50 && b >= 0 && b <= 50)
  post(result.w == a)
{
  Box x;
  x.w = a;
  x.h = b;
  return x;
}
// VERIFY: Verified: make_box
