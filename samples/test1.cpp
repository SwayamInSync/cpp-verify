spec int factorial(int n)
  decreases(n)
{
    if (n <= 1) return 1;
    return n * factorial(n - 1);
}

proof void lemma_factorial_positive(int n)
  pre(n >= 1)
  post(factorial(n) >= 1)
  decreases(n)
{
    if (n == 1) {
        // base case: factorial(1) == 1 >= 1
    } else {
        lemma_factorial_positive(n - 1);
    }
}

int safe_factorial(int n)
  pre(n >= 0)
  pre(n <= 12)
  post(result == factorial(n))
  post(result >= 1)
{
    if (n == 0) return 1;

    int acc = 1;
    int i = 1;

    while (i <= n)
      invariant(1 <= i && i <= n + 1)
      invariant(acc == factorial(i - 1))
      decreases(n - i + 1)
    {
        ghost {
            lemma_factorial_positive(i);
            contract_assert(acc * i >= acc);
        }

        acc = acc * i;
        i = i + 1;
    }

    return acc;
}

spec bool all_positive(int arr[], int n)
{
    return forall(i, 0, n, arr[i] > 0);
}

spec bool has_zero(int arr[], int n)
{
    return exists(i, 0, n, arr[i] == 0);
}

int increment(int x)
  pre(x < 2147483647)
  post(result == old(x) + 1)
{
    return x + 1;
}
