// RUN: not %cpp-verify --timeout=10000 %s 2>&1 | FileCheck %s \
// RUN:   --implicit-check-not='Verified: swing_lemma' \
// RUN:   --implicit-check-not='Verified: spec decreases: swing'
//
// Specs and proof functions that reach each other through bodies, contracts,
// and proof blocks form a cluster, as in Dafny. When they share a measure,
// every call between them lowers it, and a definition or postcondition of
// one is used only where the measure is lower, so they are proved together
// by well-founded induction. Without one, a proof that rests on another of
// them is a cycle.

#include <cppverify.h>

// The spec's postcondition is proved by a lemma about the spec, at a lower
// measure; the lemma uses the spec's definition at the same argument, which
// the second component of the measures puts below it.
proof void total_nonneg(int n);

spec int total(int n)
  decreases(n, 0)
  post(result >= 0) by { if (n > 0) total_nonneg(n - 1); }
{
  return n <= 0 ? 0 : total(n - 1) + n;
}

proof void total_nonneg(int n)
  decreases(n, 1)
  post(total(n) >= 0)
{
  if (n > 0)
    total_nonneg(n - 1);
}
// CHECK-DAG: Verified: spec decreases and post: total
// CHECK-DAG: Verified: total_nonneg

// With equal measures the lemma cannot unfold the spec at its own argument,
// and the message says what would let it.
proof void sum_nonneg(int n);

spec int sum(int n)
  decreases(n)
  post(result >= 0) by { if (n > 0) sum_nonneg(n - 1); }
{
  return n <= 0 ? 0 : sum(n - 1) + n;
}

proof void sum_nonneg(int n)
  decreases(n)
  post(sum(n) >= 0)
{
  if (n > 0)
    sum_nonneg(n - 1);
}
// CHECK-DAG: Unresolved: sum_nonneg [backend=z3] [reason=spec.hidden] {{.*}}sum shares a cluster with sum_nonneg, whose members use each other's definitions only where the measure is lower
// CHECK-DAG: Unresolved: spec decreases and post: sum [reason=callee.contract]

// A lemma that would hold only by itself: its call does not lower the
// measure, and the postcondition it would use is not available at the same
// measure.
proof void lie_lemma(int n);

spec int lie(int n)
  decreases(n)
  post(result > 0) by { lie_lemma(n); }
{
  return 0;
}

proof void lie_lemma(int n)
  decreases(n)
  post(lie(n) > 0)
{
}
// CHECK-DAG: error: verification failed: lie_lemma {{.*}}[reason=counterexample]
// CHECK-DAG: error: spec post failed: lie {{.*}}[reason=counterexample] {{.*}}call.lie_lemma

// Without a shared measure, two proofs that rest on each other are a
// cycle: the lemma hides the spec, so it uses the spec's postcondition,
// whose proof calls the lemma.
proof void seven_lemma(int n);

spec int seven(int n)
  post(result == 7) by { seven_lemma(n); }
{
  return 7;
}

proof void seven_lemma(int n)
  post(seven(n) == 7)
{
  ghost { hide(seven); }
}
// CHECK-DAG: Unresolved: seven_lemma {{.*}}[reason=proof.cycle] {{.*}}decreases clauses of one length

// A termination proof that would rest on a lemma about the spec's own
// definition where it diverges: the lemma may use the definition only at a
// lower measure, so it proves nothing false, and the termination proof
// rests on a lemma that is not established.
proof void swing_lemma(int k);

spec int swing(int n)
  decreases(n) by { if (n > 0) swing_lemma(n - 1); }
{
  return n <= 0 ? 0 : 1 - swing(n);
}

proof void swing_lemma(int k)
  decreases(k)
  post(false)
{
  contract_assert(swing(1) == 1 - swing(1));
}
// The lemma has no counterexample to show either: swing(1) has no value.
// CHECK-DAG: Unresolved: spec decreases: swing [reason=callee.contract]
// CHECK-DAG: Unresolved: swing_lemma
