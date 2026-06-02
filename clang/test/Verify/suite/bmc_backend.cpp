// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --backend=bmc --unroll=3 %s 2>&1 | FileCheck %s --check-prefix=VERIFY

// BMC path: loop unroll + Z3.
int sum_small(int n)
  pre(n >= 0 && n <= 2)
  post(result >= 0)
{
  int s = 0;
  int i = 0;
  while (i < n)
    invariant(s >= 0)
  {
    s = s + 1;
    i = i + 1;
  }
  return s;
}

// VERIFY: verified: sum_small