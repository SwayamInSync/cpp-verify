// RUN: %cpp-verify --backend=bmc --unroll=2 %s 2>&1 | FileCheck %s --check-prefix=VERIFY

spec int bump(int x) { return x + 1; }

int loop_mix(int n, int *p)
  pre(n >= 0 && n <= 1)
  modifies(*p)
  post(result >= 0)
{
  int i = 0;
  int s = 0;
  while (i < n)
    invariant(s >= 0)
  {
    ghost { reveal(bump); }
    contract_assert(i >= 0);
    if (i == 0)
      s = bump(s);
    else
      s = s + 0;
    *p = s;
    i = i + 1;
  }
  return s;
}

// VERIFY: Verified: loop_mix