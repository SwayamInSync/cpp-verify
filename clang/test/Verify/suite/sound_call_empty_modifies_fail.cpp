// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// A heap-modifying callee with no explicit modifies clause must still havoc the
// caller's heap (pointer param => conservatively modifies). Otherwise the caller
// could prove a false fact about the modified cell.
void inc(int* a) pre(a != nullptr && *a < 2147483647) post(*a == old(*a) + 1) { *a = *a + 1; }
int caller(int* x) pre(x != nullptr && *x < 2147483647) modifies(*x) post(*x == 999)
{ inc(x); return 0; }
// VERIFY: verification failed: caller
