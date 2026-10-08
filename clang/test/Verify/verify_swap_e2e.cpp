// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

void swap(int *a, int *b)
  cppverify::pre(a != nullptr && b != nullptr)
  cppverify::modifies(*a, *b)
  cppverify::post(*a == cppverify::old(*b) && *b == cppverify::old(*a))
{
  int t = *a;
  *a = *b;
  *b = t;
}

// VERIFY: Verified: swap