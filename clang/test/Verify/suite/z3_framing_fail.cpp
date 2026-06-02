// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=FAIL

void bad_framing(int *a, int *b)
  pre(a != nullptr && b != nullptr)
  modifies(*b)
  post(*a == old(*a))
{
  *a = 42;
}

// FAIL: verification failed: bad_framing