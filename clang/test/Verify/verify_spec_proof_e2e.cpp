// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

// Exercises a recursive spec function, an inductive proof lemma, and a loop
// whose invariant is stated against the spec — all verified soundly.
//
// NOTE: the loop invariant relates `acc` to the spec via `acc == count(i - 1)`,
// which is the *inductive* invariant under honest machine integers. A bare
// `acc >= 0` would not be preserved (it does not bound `acc`), and the original
// factorial version of this test only "verified" because an unsound loop
// encoding masked the obligation. `count(n) == n` is linear, so Z3 stays
// decidable; the step lemma must be recursive to feed Z3 the recurrence at the
// symbolic loop index.

spec int count(int n)
  decreases(n)
{
  if (n <= 0) return 0;
  return 1 + count(n - 1);
}

proof void lemma_count_step(int i)
  pre(i >= 1 && i <= 10)
  post(count(i) == 1 + count(i - 1))
  decreases(i)
{
  reveal_with_fuel(count, 10);
  if (i > 1) {
    lemma_count_step(i - 1);
  }
}

int compute_count(int n)
  pre(n >= 0 && n <= 10)
  post(result == count(n))
{
  int acc = 0;
  int i = 1;
  while (i <= n)
    invariant(i >= 1 && i <= n + 1 &&
              acc == i - 1 && acc == count(i - 1))
    decreases(n - i + 1)
  {
    ghost {
      reveal_with_fuel(count, 2);
      lemma_count_step(i);
    }
    acc = acc + 1;
    i = i + 1;
  }
  return acc;
}

// VERIFY: spec decreases: count
// VERIFY-DAG: Verified: lemma_count_step
// VERIFY-DAG: Verified: compute_count
