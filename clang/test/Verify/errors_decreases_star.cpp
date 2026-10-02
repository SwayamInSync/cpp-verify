// RUN: %clang_cc1 -std=c++17 -fverify-contracts -verify %s
//
// decreases(*) allows divergence, which a spec or proof function never may,
// and a measure cannot be both given and waived.

proof void lemma(int n)
  decreases(*) // expected-error {{proof functions must terminate; decreases(*) is not allowed}}
{
}

spec int value(int n)
  decreases(*) // expected-error {{spec functions must terminate; decreases(*) is not allowed}}
{
  return n;
}

void both(int n)
  decreases(n)
  decreases(*) // expected-error {{decreases(*) allows divergence and cannot be combined with a measure}}
{
}

void loop_both(int n) {
  while (n > 0)
    decreases(*)
    decreases(n) // expected-error {{decreases(*) allows divergence and cannot be combined with a measure}}
  {
    n = n - 1;
  }
}
