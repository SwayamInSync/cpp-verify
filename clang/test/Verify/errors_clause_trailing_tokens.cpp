// RUN: %clang_cc1 -std=c++17 -fverify-contracts -fsyntax-only -verify %s
//
// Tokens left between a clause's expression and its ')' are an error, never
// dropped: the clause that would be proved is not the clause as written.

namespace cv = cppverify;

int no_and(int x)
  cv::post(cv::result >= 0 // expected-note {{to match this '('}}
           cv::result <= 255) // expected-error {{expected ')' after cppverify::post expression}}
{
  return x;
}

int pre_missing_op(int x)
  cv::pre(x > 0 x < 10) // expected-error {{expected ')' after cppverify::pre expression}} expected-note {{to match this '('}}
{
  return x;
}

int stray(int x)
  cv::post(cv::result > 0 ; garbage) // expected-error {{expected ')' after cppverify::post expression}} expected-note {{to match this '('}}
{
  return 1;
}

int down(int n)
  cv::decreases(n n) // expected-error {{expected ')' after cppverify::decreases expression}} expected-note {{to match this '('}}
{
  return n <= 0 ? 0 : down(n - 1);
}

void framed(int *p, int *q)
  cv::modifies(*p q) // expected-error {{expected ')' after cppverify::modifies expression}} expected-note {{to match this '('}}
{
  *p = 0;
}

void aliased(int *p, int *q)
  cv::aliases(p, q q) // expected-error {{expected ')' after cppverify::aliases expression}} expected-note {{to match this '('}}
  cv::modifies(*p)
{
  *p = *q;
}

cv::spec int sum(const int *a, int n)
  cv::reads(a, n n) // expected-error {{expected ')' after cppverify::reads expression}} expected-note {{to match this '('}}
  cv::decreases(n)
{
  return n <= 0 ? 0 : sum(a, n - 1) + a[n - 1];
}

cv::spec int quotient(int a, int b)
  cv::recommends(b != 0 b > 0) // expected-error {{expected ')' after cppverify::recommends expression}} expected-note {{to match this '('}}
{
  return a / b;
}

cv::spec int partial(int n)
  cv::when(n >= 0 n < 10) // expected-error {{expected ')' after cppverify::when expression}} expected-note {{to match this '('}}
{
  return n;
}

// A clause whose expression is itself malformed gets that one error only.
int bad_expression(int x)
  cv::pre(x > ) // expected-error {{expected expression}}
{
  return x;
}

// Well-formed clauses are unaffected.
int fine(int x)
  cv::pre(x >= 0 && x < 100)
  cv::post(cv::result == x + 1)
{
  return x + 1;
}
