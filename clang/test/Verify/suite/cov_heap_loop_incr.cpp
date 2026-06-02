// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int loop_incr(int n, int *p)
  pre(n >= 0 && n <= 2)
  modifies(*p)
  post(result >= 0)
{
  int i = 0;
  while (i < n)
    invariant(i >= 0)
  {
    *p = *p + 1;
    i = i + 1;
  }
  return i;
}

// VERIFY: Verified: loop_incr