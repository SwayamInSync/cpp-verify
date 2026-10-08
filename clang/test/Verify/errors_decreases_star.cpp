// RUN: %clang_cc1 -std=c++17 -fverify-contracts -verify %s
//
// decreases(*) allows divergence, which a spec or proof function never may,
// and a measure cannot be both given and waived.

cppverify::proof void lemma(int n)
  cppverify::decreases(*) // expected-error {{proof functions must terminate; cppverify::decreases(*) is not allowed}}
{
}

cppverify::spec int value(int n)
  cppverify::decreases(*) // expected-error {{spec functions must terminate; cppverify::decreases(*) is not allowed}}
{
  return n;
}

void both(int n)
  cppverify::decreases(n)
  cppverify::decreases(*) // expected-error {{cppverify::decreases(*) allows divergence and cannot be combined with a measure}}
{
}

void loop_both(int n) {
  while (n > 0)
    cppverify::decreases(*)
    cppverify::decreases(n) // expected-error {{cppverify::decreases(*) allows divergence and cannot be combined with a measure}}
  {
    n = n - 1;
  }
}
