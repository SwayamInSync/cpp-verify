// RUN: %clang_cc1 -std=c++17 -fverify-contracts -verify %s
//
// Negative tests: parsing errors for contract constructs.
// Missing parens, braces, commas, etc.

// ---------------------------------------------------------------------------
// 1. ghost without brace
// ---------------------------------------------------------------------------
int f1(int x) {
  ghost x; // expected-error {{expected '{' after ghost}} expected-warning {{expression result unused}}
  return x;
}

// ---------------------------------------------------------------------------
// 2. contract_assert without parens
// ---------------------------------------------------------------------------
int f2(int x) {
  ghost {
    contract_assert x > 0; // expected-error {{expected '(' after 'contract_assert'}} expected-warning {{relational comparison result unused}}
  }
  return x;
}
