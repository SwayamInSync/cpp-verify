// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Fuel-parameterized recursive spec axioms: a one-step unfold of a recursive
// spec (fibo's defining equation) verifies for a symbolic argument, and a
// concrete value reduces correctly. This is the sound replacement for the old
// opaque-leaf axiom that could not pin a recursive spec down.
spec int fibo(int n) decreases(n)
{ if (n == 0) return 0; if (n == 1) return 1; return fibo(n - 2) + fibo(n - 1); }

proof void fibo_step(int i) pre(i >= 1) post(fibo(i + 1) == fibo(i) + fibo(i - 1)) { }
// VERIFY: Verified: fibo_step

proof void fibo_six() post(fibo(6) == 8) { reveal_with_fuel(fibo, 8); }
// VERIFY: Verified: fibo_six
