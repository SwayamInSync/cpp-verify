// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int inc(int x)
  pre(x >= 0 && x < 1000)
  post(result == x + 1)
{
  return x + 1;
}

int use_inc(int x)
  pre(x >= 0 && x < 999)
  post(result == x + 1)
{
  return inc(x);
}

// VERIFY-DAG: verified: inc
// VERIFY-DAG: verified: use_inc