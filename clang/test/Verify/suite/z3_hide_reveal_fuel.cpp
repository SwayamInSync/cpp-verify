// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

spec int triple(int x) { return 3 * x; }

proof void lemma_triple(int x)
  pre(x >= 0 && x <= 50)
  post(triple(x) == 3 * x)
{
  ghost { reveal(triple); }
}

int client_reveal(int x)
  pre(x >= 0 && x <= 10)
  post(result == triple(x))
{
  ghost { reveal(triple); }
  return x + x + x;
}

int client_hide(int x)
  pre(x >= 0 && x <= 10)
  post(result == x + x + x)
{
  ghost { hide(triple); }
  return x + x + x;
}

spec int fact(int n)
  decreases(n)
{
  if (n <= 1) return 1;
  return n * fact(n - 1);
}

proof void lemma_fact_base(int n)
  pre(n == 0)
  post(fact(n) == 1)
{
  ghost { reveal_with_fuel(fact, 2); }
}

// VERIFY-DAG: spec axiom: triple
// VERIFY-DAG: verified: lemma_triple
// VERIFY-DAG: verified: client_reveal
// VERIFY-DAG: verified: client_hide
// VERIFY-DAG: spec decreases: fact
// VERIFY-DAG: verified: lemma_fact_base