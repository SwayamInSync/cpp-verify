// RUN: not %cpp-verify --timeout=10000 --int-encoding=bitvector %s -- 2>&1 | FileCheck %s
//
// A disputed model makes the verifier probe the least and greatest values the
// query allows for the disputed applications' arguments, where a model may be
// a real counterexample. Every bit-vector check of this probe is slow, and the
// first extreme it tries is never proved; the counterexample at the least
// values is found because the probe is bounded by its checks, not by a share
// of the refinement slice, so the machine's speed does not decide it. The
// precondition keeps the solver's first models far from the counterexamples.

#include <cppverify.h>

cppverify::spec int fibo(int n)
  cppverify::decreases(n)
  cppverify::post(cppverify::result >= 0)
{
  if (n <= 0) return 0;
  if (n == 1) return 1;
  return fibo(n - 2) + fibo(n - 1);
}

cppverify::proof void far_strict(int i, int j)
  cppverify::pre(i < j && (i > 2500 || i < -2000000000))
  cppverify::post(fibo(i) < fibo(j))
  cppverify::decreases(j - i)
{
  if (i < j - 1)
    far_strict(i, j - 1);
}
// CHECK: error: verification failed: far_strict {{.*}}(counterexample: i [ssa=i_0] [type=i32] = -2147483648, j [ssa=j_0] [type=i32] = -2147483647{{.*}}[reason=counterexample]
