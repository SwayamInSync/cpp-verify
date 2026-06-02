// Executable example: normal C++ compile strips spec/proof/ghost.
// Only `main` and `compute_sum` end up in the binary.

#include <cstdio>

spec int sum_spec(int n)
  decreases(n)
{
  if (n <= 0)
    return 0;
  return n + sum_spec(n - 1);
}

proof void lemma_sum_nonneg(int n)
  pre(n >= 0)
  post(sum_spec(n) >= 0)
  decreases(n)
{
  if (n != 0)
    lemma_sum_nonneg(n - 1);
}

int compute_sum(int n)
  pre(n >= 0)
  pre(n <= 100)
  post(result >= 0)
  post(result == sum_spec(n))
{
  ghost {
    lemma_sum_nonneg(n);
    contract_assert(sum_spec(n) >= 0);
  }
  int s = 0;
  for (int i = 0; i < n; ++i)
    s += i + 1;
  return s;
}

int main() {
  int x = 10;
  int r = compute_sum(x);
  std::printf("sum(1..%d) = %d\n", x, r);
  return 0;
}