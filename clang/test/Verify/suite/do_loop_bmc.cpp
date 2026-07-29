// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --backend=bmc --unroll=3 %s 2>&1 | FileCheck %s

int count_to_bounded(int n)
  pre(n >= 0 && n <= 3)
  post(result == n + 1)
{
  int value = 0;
  do {
    value = value + 1;
  } while (value <= n)
    invariant(value >= 1 && value <= n + 1)
    decreases(n + 1 - value);
  return value;
}

// CHECK: Verified: count_to_bounded
