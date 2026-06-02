// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

spec int factorial(int n)
  decreases(n)
{
  if (n <= 1) return 1;
  return n * factorial(n - 1);
}

proof void lemma_factorial_positive(int n)
  pre(n >= 1)
  post(n >= 1)
  decreases(n)
{
  if (n == 1) {
  } else {
    lemma_factorial_positive(n - 1);
  }
}

int compute_factorial(int n)
  pre(n >= 0 && n <= 5)
  post(result >= 1)
{
  ghost {
    reveal_with_fuel(factorial, 5);
    lemma_factorial_positive(n);
  }
  int acc = 1;
  int i = 1;
  while (i <= n)
    invariant(acc >= 1)
    invariant(i >= 1)
    decreases(n - i + 1)
  {
    acc = acc * i;
    i = i + 1;
  }
  return acc;
}

// VERIFY: spec decreases: factorial
// VERIFY: Verified: lemma_factorial_positive
// VERIFY-DAG: Verified: compute_factorial