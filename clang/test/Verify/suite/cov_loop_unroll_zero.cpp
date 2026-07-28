// RUN: not %cpp-verify --backend=bmc --unroll=0 %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: %cpp-verify --lower-only --backend=bmc --unroll=0 --dump-ir=3 %s 2>&1 | FileCheck %s --check-prefix=UNWIND

int zero_iterations(int n)
  pre(n == 0)
  post(result >= 0)
{
  int i = 0;
  while (i < n)
    invariant(i >= 0)
  {
    i = i + 1;
  }
  return i;
}

int one_step_may_run(int n)
  pre(n == 0 || n == 1)
  post(result >= 0)
{
  int i = 0;
  while (i < n)
    invariant(i >= 0)
  {
    i = i + 1;
  }
  return i;
}

// VERIFY-DAG: Verified: zero_iterations [backend=bmc, bound=0]
// VERIFY-DAG: BoundedSafe: one_step_may_run [backend=bmc, bound=0]
// UNWIND: obligation {{.*}} unwinding