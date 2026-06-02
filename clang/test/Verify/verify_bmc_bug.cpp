// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify --backend=bmc --unroll=3 %s 2>&1 | FileCheck %s --check-prefix=CHECK

int counter()
  pre(true)
  post(result == 0)
{
  int x = 0;
  int i = 0;
  while (i < 5)
    invariant(true)
  {
    x = x + 1;
    i = i + 1;
  }
  return x;
}

// CHECK: verification failed: counter