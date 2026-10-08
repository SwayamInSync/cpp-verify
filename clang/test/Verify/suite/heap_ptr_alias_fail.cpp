// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Heap soundness: without i != k, the store may alias, so preservation must
// never verify. Z3 may find the alias or conservatively time out.
void a(int* p, int i, int k, int v) cppverify::pre(p != nullptr) cppverify::modifies(*p) cppverify::post(*(p + i) == cppverify::old(*(p + i))) { *(p + k) = v; }
// VERIFY: {{(error: verification failed|Unresolved): a}}
