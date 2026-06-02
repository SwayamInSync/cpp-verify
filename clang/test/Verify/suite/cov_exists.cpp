// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int bounded(int n)
  pre(n > 0 && n <= 4)
  pre(exists(i, 0, n, i >= 0 && i < n))
  post(result >= 0)
{
  return n - 1;
}

// VERIFY: Verified: bounded