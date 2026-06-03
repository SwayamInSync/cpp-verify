// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

spec int fibo(int n)
  decreases(n)
{
  if (n == 0) return 0;
  if (n == 1) return 1;
  return fibo(n - 2) + fibo(n - 1);
}

spec bool fibo_fits_i32(int n) {
  return fibo(n) < 0x7FFFFFFF;
}

proof void lemma_fibo_step(int i)
  pre(i >= 1)
  post(fibo(i + 1) == fibo(i) + fibo(i - 1))
  decreases(i)
{
  if (i > 1) {
    reveal_with_fuel(fibo, 4);
    lemma_fibo_step(i - 1);
  }
}

int safe_fib(int n)
  pre(n >= 0 && n <= 12)
  pre(fibo_fits_i32(n))
  post(result == fibo(n))
{
  if (n <= 1) return n;

  int prev = 0;
  int cur = 1;
  int i = 1;

  while (i < n)
    invariant(1 <= i && i < n)
    invariant(prev == fibo(i - 1))
    invariant(cur == fibo(i))
    decreases(n - i)
  {
    ghost {
      reveal_with_fuel(fibo, 6);
      lemma_fibo_step(i);
    }
    int next = cur + prev;
    prev = cur;
    cur = next;
    i = i + 1;
  }
  return cur;
}

// VERIFY-DAG: Verified: safe_fib
// VERIFY-DAG: spec decreases: fibo