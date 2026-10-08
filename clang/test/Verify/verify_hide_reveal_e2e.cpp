// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s -- 2>&1 | FileCheck %s --check-prefix=VERIFY

cppverify::spec int triple(int x) { return 3 * x; }

cppverify::proof void lemma_triple(int x)
  cppverify::pre(x >= 0 && x <= 715827882)
  cppverify::post(triple(x) == 3 * x)
{
  cppverify::ghost { cppverify::reveal(triple); }
}

int client_reveal(int x)
  cppverify::pre(x >= 0 && x <= 10)
  cppverify::post(cppverify::result == triple(x))
{
  cppverify::ghost { cppverify::reveal(triple); }
  return x + x + x;
}

int client_hide(int x)
  cppverify::pre(x >= 0 && x <= 10)
  cppverify::post(cppverify::result == x + x + x)
{
  cppverify::ghost { cppverify::hide(triple); }
  return x + x + x;
}

// VERIFY: spec axiom: triple
// VERIFY: Verified: lemma_triple
// VERIFY: Verified: client_reveal
// VERIFY: Verified: client_hide