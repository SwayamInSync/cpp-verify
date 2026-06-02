// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

spec int add_one(int x) { return x + 1; }

proof void lemma_add(int x)
  pre(x >= 0)
  post(add_one(x) == x + 1)
{
}

// VERIFY: verified: lemma_add