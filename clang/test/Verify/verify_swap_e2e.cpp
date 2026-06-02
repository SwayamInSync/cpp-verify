// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

void swap(int *a, int *b)
  pre(a != nullptr && b != nullptr)
  modifies(*a, *b)
  post(*a == old(*b) && *b == old(*a))
{
  int t = *a;
  *a = *b;
  *b = t;
}

// VERIFY: Verified: swap