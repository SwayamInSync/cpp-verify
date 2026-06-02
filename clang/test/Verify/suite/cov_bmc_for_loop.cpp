// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --backend=bmc --unroll=2 %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int sum_for(int n)
  pre(n >= 0 && n <= 2)
  post(result >= 0)
{
  int s = 0;
  for (int i = 0; i < n; ++i)
    invariant(s >= 0)
    invariant(i >= 0)
  {
    s = s + 1;
  }
  return s;
}

// VERIFY: verified: sum_for