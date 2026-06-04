// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Tier-1: constructing and returning a struct that violates its type_invariant
// is caught at the return point (h may be negative).
struct Box {
  int w;
  int h;
  type_invariant(w >= 0 && h >= 0);
};

Box make_bad(int a, int b)
  pre(a >= 0 && a <= 50 && b <= 50)   // b may be negative
{
  Box x;
  x.w = a;
  x.h = b;
  return x;
}
// VERIFY: verification failed
