// RUN: %clang_cc1 -std=c++17 -fverify-contracts -fno-verify -verify %s
//
// A function template's contract is checked where it is instantiated, as its
// body is, so an error names the specialization. A template whose contract
// some arguments would break is no error until one of them is used.

struct Pair {
  int first;
  int second;
};

template <typename T>
int first_of(T v)
  cppverify::post(cppverify::result == v.first) // expected-error {{member reference base type 'int' is not a structure or union}}
{
  return 0;
}

int uses_first() {
  Pair p{1, 2};
  return first_of(p) + first_of(3); // expected-note {{in instantiation of function template specialization 'first_of<int>' requested here}}
}

template <typename T>
void needs(T v)
  cppverify::pre(v) // expected-error {{value of type 'Pair' is not contextually convertible to 'bool'}}
{
}

void uses_needs() {
  needs(1);
  needs(Pair{1, 2}); // expected-note {{in instantiation of function template specialization 'needs<Pair>' requested here}}
}

template <typename T>
int steps(T p)
  cppverify::decreases(p) // expected-error {{decreases expression must have integer type}}
{
  return 0;
}

int uses_steps() {
  int x = 0;
  return steps(1) + steps(&x); // expected-note {{in instantiation of function template specialization 'steps<int *>' requested here}}
}

template <typename T>
bool all_below(const int *p, T n)
  cppverify::pre(cppverify::forall(k, 0, n, p[k] < 10)) // expected-error {{quantifier bound must have integer type}}
{
  return true;
}

bool uses_all_below(const int *p) {
  return all_below(p, 3) && all_below(p, 2.5); // expected-note {{in instantiation of function template specialization 'all_below<double>' requested here}}
}

template <typename T>
void fills(T *p, T n)
  cppverify::modifies(p[0 : n]) // expected-error {{a modifies range length must have integer type}}
{
}

void uses_fills(int *p, double *q) {
  fills(p, 2);
  fills(q, 2.0); // expected-note {{in instantiation of function template specialization 'fills<double>' requested here}}
}

// In the body, an assertion and a loop invariant are conditions too.
template <typename T>
void asserts(T v) {
  cppverify::check(v); // expected-error {{value of type 'Pair' is not contextually convertible to 'bool'}}
}

template <typename T>
void loops(T v) {
  for (int i = 0; i < 3; i = i + 1)
    cppverify::invariant(v) // expected-error {{value of type 'Pair' is not contextually convertible to 'bool'}}
    cppverify::decreases(3 - i)
  {
  }
}

void uses_body() {
  asserts(1);
  asserts(Pair{1, 2}); // expected-note {{in instantiation of function template specialization 'asserts<Pair>' requested here}}
  loops(1);
  loops(Pair{1, 2}); // expected-note {{in instantiation of function template specialization 'loops<Pair>' requested here}}
}

// Used only with arguments its contract fits.
template <typename T>
int only_records(T v)
  cppverify::post(cppverify::result == v.first)
{
  return v.first;
}

int uses_only_records() {
  Pair p{1, 2};
  return only_records(p);
}

// An unevaluated use asks for no contract.
template <typename T>
int records_only(T v)
  cppverify::post(cppverify::result == v.first)
{
  return v.first;
}

using Unevaluated = decltype(records_only(3));
