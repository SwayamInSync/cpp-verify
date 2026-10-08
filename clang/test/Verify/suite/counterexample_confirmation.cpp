// RUN: not %cpp-verify --timeout=10000 %s -- 2>&1 | FileCheck %s \
// RUN:   --implicit-check-not='failed: true_at_large' \
// RUN:   --implicit-check-not='failed: depth_below_zero' \
// RUN:   --implicit-check-not='failed: total_of_negatives'
// RUN: not %cpp-verify --timeout=10000 --diagnostics-format=json %s -- 2>&1 \
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

cppverify::spec int pow2(int n)
  cppverify::decreases(n)
  cppverify::post(cppverify::result >= n + 1)
{
  return n <= 0 ? 1 : 2 * pow2(n - 1);
}

// False everywhere: pow2(n) >= n + 1 > 1000. Every counterexample is at
// least a billion.
cppverify::proof void small_power(int n)
  cppverify::pre(n >= 1000000000)
  cppverify::post(pow2(n) < 1000)
{
}
// CHECK-DAG: error: verification failed: small_power {{.*}}(counterexample: n [ssa=n_0] [type=i32] = {{[0-9]+}}; confirmed by a proof at this input, since its check could not compute pow2({{[0-9]+}})) [backend=z3] [reason=counterexample]

cppverify::spec int fibo(int n)
  cppverify::decreases(n)
  cppverify::post(cppverify::result >= 0)
{
  if (n <= 0) return 0;
  if (n == 1) return 1;
  return fibo(n - 2) + fibo(n - 1);
}

// The fact that settles the next claim, proved as a lemma.
cppverify::proof void fibo_at_least_5(int n)
  cppverify::pre(n >= 5)
  cppverify::post(fibo(n) >= 5)
  cppverify::decreases(n)
{
  if (n >= 6)
    fibo_at_least_5(n - 1);
}

cppverify::proof void fibo_small(int n)
  cppverify::pre(n >= 1000000000)
  cppverify::post(fibo(n) < 5)
{
}
// CHECK-DAG: error: verification failed: fibo_small {{.*}}(counterexample: n [ssa=n_0] [type=i32] = 1000000000; confirmed by a proof at this input that uses the contract of fibo_at_least_5, since its check could not compute fibo(1000000000)) [backend=z3] [reason=counterexample]
// JSON-DAG: "confirmed_with":["fibo_at_least_5"]

// The same with a lemma that does not hold: a confirmation uses only the
// contracts that are established, once every function is verified, so
// nothing settles this claim.
cppverify::spec int fib2(int n)
  cppverify::decreases(n)
  cppverify::post(cppverify::result >= 0)
{
  if (n <= 0) return 0;
  if (n == 1) return 1;
  return fib2(n - 2) + fib2(n - 1);
}

cppverify::proof void fib2_at_least_5(int n)
  cppverify::pre(n >= 4)
  cppverify::post(fib2(n) >= 5)
  cppverify::decreases(n)
{
  if (n >= 6)
    fib2_at_least_5(n - 1);
}
// CHECK-DAG: error: verification failed: fib2_at_least_5

cppverify::proof void fib2_small(int n)
  cppverify::pre(n >= 1000000000)
  cppverify::post(fib2(n) < 5)
{
}
// CHECK-DAG: Unresolved: fib2_small [backend=z3] [reason=spec.fuel] {{.*}}no proved fact settles it

// Without such a fact nothing confirms it, and the claim may as well be true
// for want of a lemma: the message shows the input and both possibilities.
cppverify::spec int fib3(int n)
  cppverify::decreases(n)
  cppverify::post(cppverify::result >= 0)
{
  if (n <= 0) return 0;
  if (n == 1) return 1;
  return fib3(n - 2) + fib3(n - 1);
}

cppverify::proof void fib3_small(int n)
  cppverify::pre(n >= 1000000000)
  cppverify::post(fib3(n) < 5)
{
}
// CHECK-DAG: Unresolved: fib3_small [backend=z3] [reason=spec.fuel] (proof obligation {{.*}}: Z3 proposed n = 1000000000 as a counterexample, but checking it needs fib3(1000000000) ({{.*}}), and no proved fact settles it: either the claim is false there, or it is true and needs a proof by induction; {{.*}}a proof by induction following fib3 could start from the body 'if (n > 0 && n != 1 && n - 2 >= 1000000000 && n - 1 >= 1000000000) { fib3_small(n - 2); fib3_small(n - 1); }', with cppverify::decreases(n))
// JSON-DAG: "function":"fib3_small"{{.*}}"unchecked_counterexample":{"application":"fib3(1000000000)","model":[{"name":"n","ssa":"n_0","type":"i32","value":"1000000000"}]}

// A true claim is never confirmed as failing, however large its inputs:
// the lemma makes fibo(n) >= 5 there, which leaves no counterexample.
cppverify::proof void true_at_large(int n)
  cppverify::pre(n >= 1000000000)
  cppverify::post(fibo(n) >= 5)
{
}
// CHECK-DAG: Unresolved: true_at_large

// A spec's own checks are confirmed the same way: the lemma's machine
// parameter is matched against the spec's mathematical argument.
cppverify::spec int capped(int n)
  cppverify::post(n < 1000000000 || cppverify::result < 5)
{
  return fibo(n);
}
// CHECK-DAG: error: spec post failed: capped [backend=z3] [reason=counterexample] (n [type=math-i32] = 1000000000; confirmed by a proof at this input that uses the contract of fibo_at_least_5, since its check could not compute fibo(1000000000))

// A lemma is used through what its verification proved: its postconditions
// wherever every assumption its proof started from holds. Besides its own
// preconditions these are the generated ones, such as a pointer being null
// or valid, the extent valid(p, n) gives, distinct objects for mutable
// pointers, and type invariants. A parameter the match leaves open (the
// pointer below) ranges over every value, so the lemma applies wherever
// some value meets those assumptions: null does here.
cppverify::spec int fib4(int n)
  cppverify::decreases(n)
  cppverify::post(cppverify::result >= 0)
{
  if (n <= 0) return 0;
  if (n == 1) return 1;
  return fib4(n - 2) + fib4(n - 1);
}

cppverify::proof void fib4_at_least_5(const int *unused, int n)
  cppverify::pre(n >= 5)
  cppverify::post(fib4(n) >= 5)
  cppverify::decreases(n)
{
  if (n >= 6)
    fib4_at_least_5(unused, n - 1);
}

cppverify::proof void fib4_small(int n)
  cppverify::pre(n >= 1000000000)
  cppverify::post(fib4(n) < 5)
{
}
// CHECK-DAG: Verified: fib4_at_least_5
// CHECK-DAG: error: verification failed: fib4_small {{.*}}(counterexample: n [ssa=n_0] [type=i32] = 1000000000; confirmed by a proof at this input that uses the contract of fib4_at_least_5, since its check could not compute fib4(1000000000)) [backend=z3] [reason=counterexample]

// The same through mutable pointers, which must be distinct objects (or
// null), and through a record whose type invariant the proof assumes.
cppverify::spec int fib5(int n)
  cppverify::decreases(n)
  cppverify::post(cppverify::result >= 0)
{
  if (n <= 0) return 0;
  if (n == 1) return 1;
  return fib5(n - 2) + fib5(n - 1);
}

cppverify::proof void fib5_at_least_5(int *a, int *b, int n)
  cppverify::pre(n >= 5)
  cppverify::post(fib5(n) >= 5)
  cppverify::decreases(n)
{
  if (n >= 6)
    fib5_at_least_5(a, b, n - 1);
}

cppverify::proof void fib5_small(int n)
  cppverify::pre(n >= 1000000000)
  cppverify::post(fib5(n) < 5)
{
}
// CHECK-DAG: error: verification failed: fib5_small {{.*}}confirmed by a proof at this input that uses the contract of fib5_at_least_5
// JSON-DAG: "confirmed_with":["fib5_at_least_5"],"function":"fib5_small"

struct Positive {
  int x;
  cppverify::type_invariant(x > 0);
};

cppverify::spec int fib6(int n)
  cppverify::decreases(n)
  cppverify::post(cppverify::result >= 0)
{
  if (n <= 0) return 0;
  if (n == 1) return 1;
  return fib6(n - 2) + fib6(n - 1);
}

cppverify::proof void fib6_at_least_5(Positive q, int n)
  cppverify::pre(n >= 5)
  cppverify::post(fib6(n) >= 5)
  cppverify::decreases(n)
{
  int seen = q.x;
  if (n >= 6)
    fib6_at_least_5(q, n - 1);
}

cppverify::proof void fib6_small(int n)
  cppverify::pre(n >= 1000000000)
  cppverify::post(fib6(n) < 5)
{
}
// CHECK-DAG: error: verification failed: fib6_small {{.*}}confirmed by a proof at this input that uses the contract of fib6_at_least_5

// Those assumptions are never dropped. depth(n) is n above zero and 0 below,
// computed one step at a time. Each lemma below states an argument is
// positive, which holds only because of an assumption its declared
// preconditions do not state: the extent valid(p, n) gives n >= 0, and the
// type invariant gives q.x > 0. Used without it at a negative argument, the
// lemma would contradict the query, and any claim would seem to fail.
cppverify::spec int depth(int n)
  cppverify::decreases(n > 0 ? n : -n)
{
  return n == 0 ? 0 : (n > 0 ? 1 + depth(n - 1) : depth(n + 1));
}

cppverify::proof void depth_by_extent(const int *p, int n)
  cppverify::pre(cppverify::valid(p, n))
  cppverify::post(n >= 0 && depth(n) + 1 > depth(n))
{
}

cppverify::proof void depth_by_invariant(Positive q)
  cppverify::post(q.x > 0 && depth(q.x) + 1 > depth(q.x))
{
  int seen = q.x;
}
// CHECK-DAG: Verified: depth_by_extent
// CHECK-DAG: Verified: depth_by_invariant

// True: depth is 0 below zero. It stays unresolved.
cppverify::proof void depth_below_zero(int n)
  cppverify::pre(n <= -1000000000)
  cppverify::post(depth(n) >= 0)
{
}
// CHECK-DAG: Unresolved: depth_below_zero

// A lemma over memory: its pointer is bound where its conclusion speaks of
// the query's application, and its premises (the extent, pointer validity,
// the elements' signs) must hold there, as the claim's own preconditions
// give them.
cppverify::spec int total(const int *a, int n)
  cppverify::reads(a, n)
  cppverify::decreases(n)
{
  return n <= 0 ? 0 : total(a, n - 1) + a[n - 1];
}

cppverify::proof void total_nonneg(const int *a, int n)
  cppverify::pre(cppverify::valid(a, n) && cppverify::forall(k, 0, n, a[k] >= 0))
  cppverify::post(total(a, n) >= 0)
  cppverify::decreases(n)
{
  if (n > 0)
    total_nonneg(a, n - 1);
}

cppverify::proof void total_negative(const int *a, int n)
  cppverify::pre(cppverify::valid(a, n) && n >= 1000000000)
  cppverify::pre(cppverify::forall(k, 0, n, a[k] >= 0))
  cppverify::post(total(a, n) < 0)
{
}
// CHECK-DAG: Verified: total_nonneg
// CHECK-DAG: error: verification failed: total_negative {{.*}}confirmed by a proof at this input that uses the contract of total_nonneg, since its check could not compute total(

// True: negative elements have a negative total. The lemma's premise does
// not hold here, so it says nothing, and the claim stays unresolved.
cppverify::proof void total_of_negatives(const int *a, int n)
  cppverify::pre(cppverify::valid(a, n) && n >= 1000000000)
  cppverify::pre(cppverify::forall(k, 0, n, a[k] < 0))
  cppverify::post(total(a, n) < 0)
{
}
// CHECK-DAG: Unresolved: total_of_negatives
