// RUN: not %cpp-verify %s 2>&1 | FileCheck %s
// RUN: not %cpp-verify --backend=bmc --unroll=1 %s 2>&1 | FileCheck %s
//
// Proof and executable functions may call each other in a cycle when every
// call within the cycle lowers one shared measure. Calls stay modular: each
// function relies on the others' contracts, which is sound once the cycle
// terminates.

bool is_odd(unsigned n);

bool is_even(unsigned n)
  decreases(n)
  post(result == (n % 2 == 0))
{
  if (n == 0)
    return true;
  return is_odd(n - 1);
}

bool is_odd(unsigned n)
  decreases(n)
  post(result == (n % 2 == 1))
{
  if (n == 0)
    return false;
  return is_even(n - 1);
}
// CHECK-DAG: Verified: is_even
// CHECK-DAG: Verified: is_odd

spec int tri(int n)
  decreases(n)
{
  return n <= 0 ? 0 : n + tri(n - 1);
}

proof void tri_odd_step(int n);

proof void tri_even_step(int n)
  pre(n >= 1 && n <= 1000)
  decreases(n)
  post(tri(n) >= n)
{
  if (n > 1)
    tri_odd_step(n - 1);
}

proof void tri_odd_step(int n)
  pre(n >= 1 && n <= 1000)
  decreases(n)
  post(tri(n) >= n)
{
  if (n > 1)
    tri_even_step(n - 1);
}
// CHECK-DAG: Verified: tri_even_step
// CHECK-DAG: Verified: tri_odd_step

// pong calls ping at the same argument, so the cycle need not terminate.
int ping(int n);

int pong(int n)
  pre(n >= 0)
  decreases(n)
  post(result == 0)
{
  if (n == 0)
    return 0;
  return ping(n);
}

int ping(int n)
  pre(n >= 0)
  decreases(n)
  post(result == 0)
{
  if (n == 0)
    return 0;
  return pong(n - 1);
}
// CHECK-DAG: error: verification failed: pong [{{.*}}::termination@{{.*}}[reason=counterexample]
// CHECK-DAG: Unresolved: ping {{.*}}[reason=callee.contract] (relies on the contract of pong, which is not established)
