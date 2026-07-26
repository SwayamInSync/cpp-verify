// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

spec int branch(int x)
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

spec int hidden_body(int x) { return x + 1; }

int use_branch(int x)
  pre(x >= -2 && x <= 2)
  post(result == branch(x))
{
  return branch(x);
}

int use_rec(int n)
  pre(n >= 0 && n <= 2)
  post(result == rec(n))
  decreases(n)
{
  ghost { reveal_with_fuel(rec, 3); }
  return rec(n);
}

// VERIFY-DAG: Verified: use_branch
// VERIFY-DAG: Verified: use_rec