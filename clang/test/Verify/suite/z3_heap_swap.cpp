// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

void swap_ptr(int *a, int *b)
  pre(a != nullptr && b != nullptr)
  modifies(*a, *b)
  post(*a == old(*b) && *b == old(*a))
{
  int tmp = *a;
  *a = *b;
  *b = tmp;
}

void write_ptr(int *p, int v)
  pre(p != nullptr)
  modifies(*p)
  post(*p == v)
{
  *p = v;
}

// VERIFY-DAG: verified: swap_ptr
// VERIFY-DAG: verified: write_ptr