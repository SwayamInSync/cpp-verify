// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY
// contract_assert(false) on a reachable path must fail.
int f(int x) cppverify::pre(x >= 0 && x <= 5) cppverify::post(cppverify::result >= 0) { cppverify::check(false); return x; }
// VERIFY: verification failed
