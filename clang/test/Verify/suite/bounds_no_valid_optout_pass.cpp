// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --check-ub %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Without a valid(p, n) declaration, bounds are not checked (opt-out): the
// access verifies because no obligation is generated for an undeclared length.
int get(int* p, int i) pre(p != nullptr && i >= 0) post(result == p[i]) { return p[i]; }
// VERIFY: Verified: get
