// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: %cpp-verify --backend=bmc --unroll=2 %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: %cpp-verify --backend=lean --lean-out=%t.lean %s 2>&1 | FileCheck %s --check-prefix=LEAN

spec int inc(int x) { return x + 1; }

spec int pick(int x)
{
  if (x < 0)
    return 0;
  return x;
}

spec int rec(int n)
  decreases(n)
{
  if (n <= 0)
    return 0;
  return rec(n - 1) + 1;
}

int exec_client(int x)
  pre(x >= 0 && x < 20)
  post(result == inc(inc(x)))
  recommends(pick(x) >= 0)
{
  ghost { reveal(inc); contract_assert(x >= 0); }
  return inc(inc(x));
}

int loop_client(int n, int *p)
  pre(n >= 0 && n <= 1)
  pre(forall(i, 0, n, i >= 0))
  modifies(*p)
  post(result >= 0)
  decreases(n)
{
  int i = 0;
  int s = 0;
  while (i < n)
    invariant(s >= 0)
    decreases(n - i)
  {
    if (i == 0)
      s = inc(s);
    *p = s;
    i = i + 1;
  }
  return s;
}

// VERIFY-DAG: verified: exec_client
// VERIFY-DAG: verified: loop_client

// LEAN: lean export: exec_client