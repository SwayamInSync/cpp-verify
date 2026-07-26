// RUN: not %clang_cc1 -std=c++17 -fverify-contracts -fsyntax-only %s 2>&1 | FileCheck %s

int duplicate_contract(int value)
  pre(value >= 0);

int duplicate_contract(int value)
  post(result >= 0)
{
  return value;
}

// CHECK: error: contract clauses may only be specified on one declaration of a function
