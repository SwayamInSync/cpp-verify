// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

cppverify::spec int triple(int x) { return 3 * x; }

cppverify::proof void lemma_triple(int x)
  cppverify::pre(x >= 0 && x <= 50)
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

cppverify::spec int fact(int n)
  cppverify::decreases(n)
{
  if (n <= 1) return 1;
  return n * fact(n - 1);
}

cppverify::proof void lemma_fact_base(int n)
  cppverify::pre(n == 0)
  cppverify::post(fact(n) == 1)
{
  cppverify::ghost { cppverify::reveal_with_fuel(fact, 2); }
}

// VERIFY-DAG: spec axiom: triple
// VERIFY-DAG: Verified: lemma_triple
// VERIFY-DAG: Verified: client_reveal
// VERIFY-DAG: Verified: client_hide
// VERIFY-DAG: spec decreases: fact
// VERIFY-DAG: Verified: lemma_fact_base