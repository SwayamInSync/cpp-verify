// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --check-ub %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// Array-bounds: p[i + 1] is in bounds and overflow-free when i < n - 1 with n
// bounded, so it verifies.
spec bool valid(int* p, int n) { return true; }
int g(int* p, int n, int i) pre(valid(p, n) && 1 <= n && n <= 1000 && 0 <= i && i < n - 1) post(result == p[i + 1]) { return p[i + 1]; }
// VERIFY: Verified: g
