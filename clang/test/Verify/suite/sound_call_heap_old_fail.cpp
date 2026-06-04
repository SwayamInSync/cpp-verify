// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// A caller of a heap-modifying function must not over-claim its effect. inc adds
// 1; the caller claiming +2 must fail. (Regression: old(*p) in the callee post
// once collapsed onto the post-state heap, yielding assume(false) and letting
// the caller prove anything.)
void inc(int* a) pre(a != nullptr) modifies(*a) post(*a == old(*a) + 1)
{ *a = *a + 1; }
int caller(int* x) pre(x != nullptr) modifies(*x) post(*x == old(*x) + 2)
{ inc(x); return 0; }
// VERIFY: verification failed: caller
