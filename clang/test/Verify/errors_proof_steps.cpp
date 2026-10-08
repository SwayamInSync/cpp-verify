// RUN: %clang_cc1 -std=c++17 -fverify-contracts -verify %s

void no_steps(int a) {
  cppverify::calc { // expected-error {{a cppverify::calc chain needs at least one step: a relation and a term}}
    a;
  }
}

void mixed(int a, int b) {
  cppverify::calc { // expected-error {{a cppverify::calc chain cannot both increase and decrease}}
    a;
    <= b;
    >= a;
  }
}

struct calc {
  int value;
};

// calc names a type here, so this is an ordinary declaration.
void type_named_calc() {
  calc c{1};
  (void)c;
}

int unknown_behavior(int x)
  cppverify::behavior(positive, x > 0)
    cppverify::post(cppverify::result > 0)
  cppverify::complete_behaviors(positive, negative) // expected-error {{no behavior named 'negative'}}
{
  return x;
}

int duplicate_behavior(int x)
  cppverify::behavior(once, x > 0)
  cppverify::behavior(once, x < 0) // expected-error {{behavior 'once' is already defined}}
{
  return x;
}

int lonely_disjoint(int x)
  cppverify::behavior(only, x > 0)
  cppverify::disjoint_behaviors // expected-error {{cppverify::disjoint_behaviors needs two behaviors}}
{
  return x;
}

int unnamed_behavior(int x)
  cppverify::behavior(x > 0) // expected-error {{expected a behavior name, then ',' and its assumption}}
{
  return x;
}

cppverify::spec int spec_behavior(int x)
  cppverify::behavior(positive, x > 0) // expected-error {{a spec function has no behaviors; state its post directly}}
{
  return x;
}

void by_needs_a_block(int a) {
  cppverify::check(a > 0) by; // expected-error {{expected ';' after cppverify::check statement}}
}
