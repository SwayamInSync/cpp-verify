// RUN: %clang_cc1 -std=c++17 -fverify-contracts -verify %s
//
// A ghost variable exists only for verification: executable code cannot read
// or write it, and a ghost declaration declares only variables.

int read_ghost(int x) {
  ghost int g = x;
  return g; // expected-error {{ghost variable 'g' exists only for verification and cannot be used in executable code; use it in a contract or ghost block}}
}

void write_ghost(int x) {
  ghost int g = 0;
  g = x; // expected-error {{ghost variable 'g' exists only for verification and cannot be used in executable code; use it in a contract or ghost block}}
}

int ghost_uses_are_fine(int x) {
  ghost int g = x;
  ghost { g = g + 1; }
  contract_assert(g == x + 1);
  return x;
}

void not_a_variable() {
  ghost struct Local { int field; }; // expected-error {{a ghost declaration must declare variables}}
}
