// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int sum_for(int n)
  pre(n >= 0 && n <= 3)
  post(result >= 0)
{
  int s = 0;
  int i = 0;
  for (; i < n;)
    invariant(s >= 0 && i >= 0)
  {
    s = s + 1;
    i = i + 1;
  }
  return s;
}

// VERIFY: verified: sum_for