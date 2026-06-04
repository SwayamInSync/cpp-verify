// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// An exists over a concrete range that cannot hold must fail: all three cells
// are set to 0, but the post claims some cell equals 9.
// (Symbolic-range exists in a postcondition is currently incomplete -- it may
// report unknown -- so this uses a concrete range.)
void f(int* p) pre(p != nullptr) modifies(*p) post(exists(i, 0, 3, p[i] == 9)) { p[0] = 0; p[1] = 0; p[2] = 0; }
// VERIFY: verification failed
