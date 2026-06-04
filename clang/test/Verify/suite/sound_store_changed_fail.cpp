// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Claiming a written cell is unchanged must fail.
void f(int* p, int v) pre(p != nullptr && v != p[2]) modifies(*p) post(p[2] == old(p[2])) { p[2] = v; }
// VERIFY: verification failed
