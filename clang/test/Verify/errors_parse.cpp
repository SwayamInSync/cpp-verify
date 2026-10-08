// RUN: %clang_cc1 -std=c++17 -fverify-contracts -verify %s
//
// Negative tests: parsing errors for contract constructs.
// Missing parens, braces, commas, etc.

// ---------------------------------------------------------------------------
// 1. ghost without brace
// ---------------------------------------------------------------------------
int f1(int x) {
  cppverify::ghost x; // expected-error {{expected '{' or a declaration after cppverify::ghost}} expected-warning {{expression result unused}}
  return x;
}

// ---------------------------------------------------------------------------
// 2. contract_assert without parens
// ---------------------------------------------------------------------------
int f2(int x) {
  cppverify::ghost {
    cppverify::check x > 0; // expected-error {{expected '(' after 'cppverify::check'}} expected-warning {{relational comparison result unused}}
  }
  return x;
}
