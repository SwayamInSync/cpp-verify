// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --backend=bmc --unroll=3 %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int sum_first_n(int n)
  pre(n >= 0 && n <= 3)
  post(result >= 0)
{
  int s = 0;
  int i = 0;
  while (i < n)
    invariant(s >= 0)
    invariant(i >= 0)
  {
    s = s + i;
    i = i + 1;
  }
  return s;
}

// VERIFY: Verified: sum_first_n