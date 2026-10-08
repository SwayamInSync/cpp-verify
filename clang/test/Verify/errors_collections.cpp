// RUN: %clang_cc1 -std=c++17 -fverify-contracts -verify %s
//
// cppverify collections exist only for verification: executable code may not
// declare, pass, return, or operate on one.

#include <cppverify.h>
using cppverify::seq;

int length() {
  seq s = cppverify::seq_empty(); // expected-error {{the cppverify type 'seq' exists only for verification and cannot be used in executable code; use it in a contract, ghost code, or a spec or proof function}} \
                                  // expected-error {{the cppverify operation 'seq_empty' exists only for verification}}
  return s.len(); // expected-error {{the cppverify operation 'len' exists only for verification}}
}

seq identity(seq s) { return s; } // expected-error {{the cppverify type 'seq' exists only for verification}} \
                                  // expected-error {{the cppverify type 'seq' exists only for verification}}

int subscript(int n) {
  cppverify::ghost seq g = cppverify::seq_of(n);
  return g[0]; // expected-error {{ghost variable 'g' exists only for verification}} \
               // expected-error {{the cppverify operation 'operator[]' exists only for verification}}
}

bool has_room(const int *p, int n) {
  return cppverify::valid(p, n); // expected-error {{the cppverify operation 'valid<int>' exists only for verification}}
}

// Ghost code, contracts, and spec and proof functions may use them.
void ghost_use(int n)
  cppverify::pre(cppverify::seq_of(n).len() == 1)
{
  cppverify::ghost seq g = cppverify::seq_empty().push(n);
  cppverify::ghost { g = g.push(n); }
  cppverify::check(g.len() == 2);
}

cppverify::spec seq twice(seq s) { return s + s; }

cppverify::proof void lemma(seq s)
  cppverify::post(twice(s).len() == 2 * s.len())
{
}
