// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// A forall over a CONCRETE range that is actually false must fail (one element
// is set to 7, the claim says all are 0).
void f(int* p) pre(p != nullptr) modifies(*p) post(forall(i, 0, 3, p[i] == 0)) { p[0] = 0; p[1] = 7; p[2] = 0; }
// VERIFY: verification failed
