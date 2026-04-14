// RUN: %clang_cc1 -std=c++17 -fverify-contracts -verify %s
//
// Negative tests: type checking errors for contract expressions.
// Non-bool conditions, non-integer bounds, non-integer decreases.

struct NotBool { int x; };

// ---------------------------------------------------------------------------
// 1. contract_assert with non-bool expression (struct)
// ---------------------------------------------------------------------------
int f1(int x) {
  NotBool s;
  ghost {
    contract_assert(s); // expected-error {{value of type 'NotBool' is not contextually convertible to 'bool'}}
  }
  return x;
}

// ---------------------------------------------------------------------------
// 2. Quantifier with float lower bound
// ---------------------------------------------------------------------------
int f2(int n)
  pre(forall(i, 0.5, n, i >= 0)) // expected-error {{quantifier bound must have integer type}}
{
  return n;
}

// ---------------------------------------------------------------------------
// 3. Quantifier with float upper bound
// ---------------------------------------------------------------------------
int f3(int n)
  pre(forall(i, 0, 1.5, i >= 0)) // expected-error {{quantifier bound must have integer type}}
{
  return n;
}

// ---------------------------------------------------------------------------
// 4. decreases on while loop with float literal
// ---------------------------------------------------------------------------
int f4(int n) {
  int i = 0;
  while (i < n)
    decreases(1.5) // expected-error {{decreases expression must have integer type}}
  {
    i++;
  }
  return i;
}

// ---------------------------------------------------------------------------
// 5. decreases on for loop with float literal
// ---------------------------------------------------------------------------
int f5(int n) {
  for (int i = 0; i < n; i++)
    decreases(0.5) // expected-error {{decreases expression must have integer type}}
  {
  }
  return n;
}

// ---------------------------------------------------------------------------
// 6. decreases on spec function with float
// ---------------------------------------------------------------------------
spec int f6(int n)
  decreases(1.0) // expected-error {{decreases expression must have integer type}}
{
  return n;
}
