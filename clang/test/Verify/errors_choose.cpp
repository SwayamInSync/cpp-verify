// RUN: %clang_cc1 -std=c++17 -fverify-contracts -verify %s
//
// choose exists only for verification.

int executable(int n) {
  return choose(k, 0, n, k == 0); // expected-error {{choose exists only for verification and cannot be used in executable code; use it in a contract, ghost block, or spec or proof function}}
}

spec int fine(int n) { return choose(k, k == n); }

int choose(int a, int b) { return a + b; }

// With its own choose, the program calls it.
int calls_own(int n) { return choose(n, 1); }
