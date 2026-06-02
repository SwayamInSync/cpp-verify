// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

spec int hidden(int x) { return x + 1; }

int client(int x)
  pre(x >= 0 && x < 10)
  post(result == x)
{
  ghost { hide(hidden); }
  return x;
}

spec int rec(int n)
  decreases(n)
{
  if (n <= 0)
    return 0;
  return rec(n - 1) + 1;
}

int use_rec(int n)
  pre(n >= 0 && n <= 1)
  post(result == rec(n))
  decreases(n)
{
  return rec(n);
}

// VERIFY-DAG: verified: client
// VERIFY-DAG: verified: use_rec