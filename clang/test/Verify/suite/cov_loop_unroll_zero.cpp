// RUN: %cpp-verify --backend=bmc --unroll=0 %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int one_step(int n)
  pre(n == 0 || n == 1)
  post(result >= 0)
{
  int i = 0;
  while (i < n)
    invariant(i >= 0)
  {
    i = i + 1;
  }
  return i;
}

// VERIFY: Verified: one_step