// RUN: %clang_cc1 -std=c++17 -triple x86_64-pc-windows-msvc -fdelayed-template-parsing -fverify-contracts -fno-verify -fsyntax-only -verify %s
//
// With delayed template parsing, a template's body is looked at ahead for
// the name cppverify before it is kept or parsed. What is wrong with its
// tokens is reported once, where they are read for good.

template <class T> struct S {
  int v;
  S() : v(1 { } // expected-note {{to match this '('}}
}; // expected-error {{expected ')'}}
