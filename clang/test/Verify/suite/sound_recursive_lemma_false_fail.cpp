// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// A recursive proof lemma must not prove a FALSE postcondition. The inductive
// call's hypothesis is guarded by the path condition, so the contradictory IH
// on the i>0 branch cannot leak onto the base case (i==0), where i==i+1 fails.
proof void bad(int i) pre(i >= 0) post(i == i + 1) decreases(i)
{ if (i > 0) { bad(i - 1); } }
// VERIFY: verification failed: bad
