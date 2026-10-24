// RUN: %clang_cc1 -std=c++17 -fverify-contracts -fsyntax-only -verify %s
//
// The clauses of a member function are parsed in the complete-class context,
// as a function contract specifier is (C++26 [class.mem.general]): an
// in-class declaration's clauses name members declared after it and `this`,
// and an out-of-line definition's clauses are in its class's scope.

struct Counter {
  void bump()
    cppverify::pre(n < limit)
    cppverify::modifies(n)
    cppverify::post(n == cppverify::old(n) + 1 && this->limit == cppverify::old(limit))
  {
    n = n + 1;
  }

  int get() const;
  void set(int v)
    cppverify::post(n == v);

  void wrong()
    cppverify::pre(missing > 0) // expected-error {{use of undeclared identifier 'missing'}}
  {}

  int n;
  int limit;
};

int Counter::get() const
  cppverify::post(cppverify::result == this->n && limit == cppverify::old(limit))
{
  return n;
}

void Counter::set(int v) // expected-error {{contract clauses may only be specified on one declaration of a function}}
  cppverify::post(n == v)
{
  n = v;
}
