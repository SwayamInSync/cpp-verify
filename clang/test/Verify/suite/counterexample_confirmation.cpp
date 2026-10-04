// RUN: not %cpp-verify --timeout=10000 %s 2>&1 | FileCheck %s \
// RUN:   --implicit-check-not='failed: true_at_large'
// RUN: not %cpp-verify --timeout=10000 --diagnostics-format=json %s 2>&1 \
// RUN:   | FileCheck %s --check-prefix=JSON
//
// A counterexample the solver proposes is checked against the true
// definitions. When computing a value it needs is out of reach (pow2 of a
// billion has a billion bits), the counterexample is confirmed by a proof at
// its input instead: with the values it gives the source variables fixed,
// the theorems the query states assumed, and the postconditions of the
// proof functions instantiated where they speak of the same terms, the
// solver proves that the claim fails there. The failure then rests on those
// facts and contracts; where none settles it, the verdict stays unresolved
// and says why.

#include <cppverify.h>

spec int pow2(int n)
  decreases(n)
  post(result >= n + 1)
{
  return n <= 0 ? 1 : 2 * pow2(n - 1);
}

// False everywhere: pow2(n) >= n + 1 > 1000. Every counterexample is at
// least a billion.
proof void small_power(int n)
  pre(n >= 1000000000)
  post(pow2(n) < 1000)
{
}
// CHECK-DAG: error: verification failed: small_power {{.*}}(counterexample: n [ssa=n_0] [type=i32] = {{[0-9]+}}; confirmed by a proof at this input, since its check could not compute pow2({{[0-9]+}})) [backend=z3] [reason=counterexample]

spec int fibo(int n)
  decreases(n)
  post(result >= 0)
{
  if (n <= 0) return 0;
  if (n == 1) return 1;
  return fibo(n - 2) + fibo(n - 1);
}

// The fact that settles the next claim, proved as a lemma.
proof void fibo_at_least_5(int n)
  pre(n >= 5)
  post(fibo(n) >= 5)
  decreases(n)
{
  if (n >= 6)
    fibo_at_least_5(n - 1);
}

proof void fibo_small(int n)
  pre(n >= 1000000000)
  post(fibo(n) < 5)
{
}
// CHECK-DAG: error: verification failed: fibo_small {{.*}}(counterexample: n [ssa=n_0] [type=i32] = 1000000000; confirmed by a proof at this input that uses the contract of fibo_at_least_5, since its check could not compute fibo(1000000000)) [backend=z3] [reason=counterexample]
// JSON-DAG: "confirmed_with":["fibo_at_least_5"]

// The same with a lemma that does not hold: a confirmation uses only the
// contracts that are established, once every function is verified, so
// nothing settles this claim.
spec int fib2(int n)
  decreases(n)
  post(result >= 0)
{
  if (n <= 0) return 0;
  if (n == 1) return 1;
  return fib2(n - 2) + fib2(n - 1);
}

proof void fib2_at_least_5(int n)
  pre(n >= 4)
  post(fib2(n) >= 5)
  decreases(n)
{
  if (n >= 6)
    fib2_at_least_5(n - 1);
}
// CHECK-DAG: error: verification failed: fib2_at_least_5

proof void fib2_small(int n)
  pre(n >= 1000000000)
  post(fib2(n) < 5)
{
}
// CHECK-DAG: Unresolved: fib2_small [backend=z3] [reason=spec.fuel] {{.*}}no proved fact settles it

// Without such a fact nothing confirms it, and the claim may as well be true
// for want of a lemma: the message shows the input and both possibilities.
spec int fib3(int n)
  decreases(n)
  post(result >= 0)
{
  if (n <= 0) return 0;
  if (n == 1) return 1;
  return fib3(n - 2) + fib3(n - 1);
}

proof void fib3_small(int n)
  pre(n >= 1000000000)
  post(fib3(n) < 5)
{
}
// CHECK-DAG: Unresolved: fib3_small [backend=z3] [reason=spec.fuel] (proof obligation {{.*}}: Z3 proposed n = 1000000000 as a counterexample, but checking it needs fib3(1000000000) ({{.*}}), and no proved fact settles it: either the claim is false there, or it is true and needs a proof by induction; {{.*}}a proof by induction following fib3 could start from the body 'if (n > 0 && n != 1 && n - 2 >= 1000000000 && n - 1 >= 1000000000) { fib3_small(n - 2); fib3_small(n - 1); }', with decreases(n))
// JSON-DAG: "function":"fib3_small"{{.*}}"unchecked_counterexample":{"application":"fib3(1000000000)","model":[{"name":"n","ssa":"n_0","type":"i32","value":"1000000000"}]}

// A true claim is never confirmed as failing, however large its inputs:
// the lemma makes fibo(n) >= 5 there, which leaves no counterexample.
proof void true_at_large(int n)
  pre(n >= 1000000000)
  post(fibo(n) >= 5)
{
}
// CHECK-DAG: Unresolved: true_at_large

// A spec's own checks are confirmed the same way: the lemma's machine
// parameter is matched against the spec's mathematical argument.
spec int capped(int n)
  post(n < 1000000000 || result < 5)
{
  return fibo(n);
}
// CHECK-DAG: error: spec post failed: capped [backend=z3] [reason=counterexample] (n [type=math-i32] = 1000000000; confirmed by a proof at this input that uses the contract of fibo_at_least_5, since its check could not compute fibo(1000000000))

// A lemma with a pointer or reference parameter has implicit preconditions
// (valid storage, distinct objects) that its declared ones do not state, so
// its contract is not used to confirm: the claim stays unresolved.
spec int fib4(int n)
  decreases(n)
  post(result >= 0)
{
  if (n <= 0) return 0;
  if (n == 1) return 1;
  return fib4(n - 2) + fib4(n - 1);
}

proof void fib4_at_least_5(const int *unused, int n)
  pre(n >= 5)
  post(fib4(n) >= 5)
  decreases(n)
{
  if (n >= 6)
    fib4_at_least_5(unused, n - 1);
}

proof void fib4_small(int n)
  pre(n >= 1000000000)
  post(fib4(n) < 5)
{
}
// CHECK-DAG: Verified: fib4_at_least_5
// CHECK-DAG: Unresolved: fib4_small [backend=z3] [reason=spec.fuel] {{.*}}no proved fact settles it
