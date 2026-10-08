// RUN: %clang_cc1 -std=c++17 -fverify-contracts -verify %s

void no_length(int *p, int n)
  cppverify::modifies(p[1 :]) // expected-error {{a modifies range needs a length: p[start : length]}}
{
}

void not_pointer(int x)
  cppverify::modifies(x[0 : 2]) // expected-error {{a modifies range needs a pointer to a complete object type, not 'int'}}
{
}

void bool_length(int *p)
  cppverify::modifies(p[0 : true]) // expected-error {{a modifies range length must have integer type}}
{
}

void operand(int *p)
  cppverify::modifies(*p[0 : 2]) // expected-error {{a range p[start : length] is a whole modifies footprint, not an operand}}
{
}

void not_in_pre(int *p)
  cppverify::pre(p[0 : 2] == 0) // expected-error {{expected ']'}} expected-note {{to match this '['}}
{
}

void loop_range(int *p, int n) {
  for (int i = 0; i < n; i = i + 1)
    cppverify::invariant(0 <= i && i <= n)
    cppverify::modifies(p[0 : i])
    cppverify::decreases(n - i)
  {
    p[i] = 0;
  }
}
