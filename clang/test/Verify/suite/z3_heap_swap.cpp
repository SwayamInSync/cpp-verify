// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

void swap_ptr(int *a, int *b)
  cppverify::pre(a != nullptr && b != nullptr)
  cppverify::modifies(*a, *b)
  cppverify::post(*a == cppverify::old(*b) && *b == cppverify::old(*a))
{
  int tmp = *a;
  *a = *b;
  *b = tmp;
}

void write_ptr(int *p, int v)
  cppverify::pre(p != nullptr)
  cppverify::modifies(*p)
  cppverify::post(*p == v)
{
  *p = v;
}

// VERIFY-DAG: Verified: swap_ptr
// VERIFY-DAG: Verified: write_ptr