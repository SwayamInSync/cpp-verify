// RUN: %clang_cc1 -std=c++17 -fverify-contracts -verify %s

void no_steps(int a) {
  calc { // expected-error {{a calc chain needs at least one step: a relation and a term}}
    a;
  }
}

void mixed(int a, int b) {
  calc { // expected-error {{a calc chain cannot both increase and decrease}}
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
  behavior(positive, x > 0)
    post(result > 0)
  complete_behaviors(positive, negative) // expected-error {{no behavior named 'negative'}}
{
  return x;
}

int duplicate_behavior(int x)
  behavior(once, x > 0)
  behavior(once, x < 0) // expected-error {{behavior 'once' is already defined}}
{
  return x;
}

int lonely_disjoint(int x)
  behavior(only, x > 0)
  disjoint_behaviors // expected-error {{disjoint_behaviors needs two behaviors}}
{
  return x;
}

int unnamed_behavior(int x)
  behavior(x > 0) // expected-error {{expected a behavior name, then ',' and its assumption}}
{
  return x;
}

spec int spec_behavior(int x)
  behavior(positive, x > 0) // expected-error {{a spec function has no behaviors; state its post directly}}
{
  return x;
}

void by_needs_a_block(int a) {
  contract_assert(a > 0) by; // expected-error {{expected ';' after contract_assert}}
}
