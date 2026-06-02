// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=CHECK

spec int need_pos(int x)
  recommends(x > 0)
{
  return x;
}

int caller(int x)
  pre(x == 0)
  post(result > 0)
{
  return need_pos(x);
}

// CHECK: verification failed: caller