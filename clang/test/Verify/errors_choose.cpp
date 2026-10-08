// RUN: %clang_cc1 -std=c++17 -fverify-contracts -verify %s
//
// cppverify::choose exists only for verification.

int executable(int n) {
  return cppverify::choose(k, 0, n, k == 0); // expected-error {{cppverify::choose exists only for verification and cannot be used in executable code; use it in a contract, ghost block, or spec or proof function}}
}

cppverify::spec int fine(int n) { return cppverify::choose(k, k == n); }

// A bare choose is the program's own.
int choose(int a, int b) { return a + b; }
int calls_own(int n) { return choose(n, 1); }
