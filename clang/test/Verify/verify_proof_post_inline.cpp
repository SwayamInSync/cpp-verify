// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

cppverify::spec int add_one(int x) { return x + 1; }

cppverify::proof void lemma_add(int x)
  cppverify::pre(x >= 0 && x < 2147483647)
  cppverify::post(add_one(x) == x + 1)
{
}

// VERIFY: Verified: lemma_add