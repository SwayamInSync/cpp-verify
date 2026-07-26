// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

spec int triple(int x) { return 3 * x; }

proof void lemma_triple(int x)
  pre(x >= 0 && x <= 715827882)
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

// VERIFY: spec axiom: triple
// VERIFY: Verified: lemma_triple
// VERIFY: Verified: client_reveal
// VERIFY: Verified: client_hide