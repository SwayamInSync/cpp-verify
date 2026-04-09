spec int fibo(int n) decreases(n) {
    if (n <= 1) return n;
    return fibo(n - 1) + fibo(n - 2);
}

int safe_fib(int n)
  pre(n >= 0)
  pre(n <= 45)
  post(result == fibo(n))
{
    if (n <= 1) return n;
    int a = 0, b = 1, i = 2;
    while (i <= n)
      invariant(2 <= i && i <= n + 1)
      invariant(b == fibo(i - 1))
      decreases(n - i + 1)
    {
        int tmp = a + b;
        a = b;
        b = tmp;
        i++;
    }
    return b;
}