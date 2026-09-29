// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=CHECK

spec int need_pos(int x)
  recommends(x > 0)
{
  return x;
}

int caller(int x)
  pre(x == 0)
  post(result >= 0)
{
  ghost {
    int checked = need_pos(x);
    contract_assert(checked > 0);
  }
  return x;
}

// CHECK: verification failed: caller