// RUN: %clang_cc1 -std=c++17 -fverify-contracts -verify %s
// RUN: %clang_cc1 -std=c++17 -fverify-contracts -fno-verify -DALLOWED_ONLY \
// RUN:   -emit-llvm -o - %s | FileCheck %s --implicit-check-not=poison
//
// A quantifier has no value at run time, so executable code may not use one;
// it once compiled to poison. Contracts, ghost code, and unevaluated operands
// may.

// CHECK: define {{.*}}allowed
bool allowed(int n)
  cppverify::pre(cppverify::forall(k, 0, n, k >= 0))
  cppverify::post(cppverify::result == cppverify::exists(k, 0, n, k == 0))
{
  cppverify::check(cppverify::forall(k, 0, 1, k == 0));
  cppverify::ghost { bool all = cppverify::forall(k, 0, n, k >= 0); }
  unsigned long size = sizeof(cppverify::forall(k, 0, n, k >= 0));
  return n > 0 && size == sizeof(bool);
}

#ifndef ALLOWED_ONLY
bool returns_forall(int n) {
  return cppverify::forall(k, 0, n, k >= 0); // expected-error {{cppverify::forall exists only for verification and cannot be used in executable code; use it in a contract, ghost block, or spec or proof function}}
}

bool initializes_exists(int n) {
  bool found = cppverify::exists(k, 0, n, k == 3); // expected-error {{cppverify::exists exists only for verification}}
  return found;
}

// The inner quantifier is reported with the outer one.
bool nested(int n) {
  return cppverify::forall(i, 0, n, cppverify::exists(j, 0, n, i == j)); // expected-error {{cppverify::forall exists only for verification}}
}

bool global_quantifier = cppverify::exists(k, 0, 2, k == 1); // expected-error {{cppverify::exists exists only for verification}}
#endif
