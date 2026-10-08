// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Fuel-parameterized recursive spec axioms: a one-step unfold of a recursive
// spec (fibo's defining equation) verifies for a symbolic argument, and a
// concrete value reduces correctly. This is the sound replacement for the old
// opaque-leaf axiom that could not pin a recursive spec down.
cppverify::spec int fibo(int n) cppverify::decreases(n)
{ if (n <= 0) return 0; if (n == 1) return 1; return fibo(n - 2) + fibo(n - 1); }

cppverify::proof void fibo_step(int i) cppverify::pre(i >= 1 && i <= 10) cppverify::post(fibo(i + 1) == fibo(i) + fibo(i - 1)) { }
// VERIFY: Verified: fibo_step

cppverify::proof void fibo_six() cppverify::post(fibo(6) == 8) { cppverify::reveal_with_fuel(fibo, 8); }
// VERIFY: Verified: fibo_six
