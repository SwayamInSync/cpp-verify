// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

int inc(int x)
  pre(x >= 0 && x < 100)
  post(result == x + 1)
{
  return x + 1;
}

int bump(int x)
  pre(x >= 0 && x < 99)
  post(result >= x)
{
  if (x < 50)
    return inc(x);
  return inc(inc(x));
}

// VERIFY-DAG: verified: inc
// VERIFY-DAG: verified: bump