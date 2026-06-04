// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Ultimate vacuity check: post(false) with a SATISFIABLE precondition must be
// rejected (if it verified, the prover would be unsound on everything).
int f(int x) pre(x >= 0 && x <= 10) post(false) { return x; }
// VERIFY: verification failed
