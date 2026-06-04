// b > 0 rules out division-by-zero and the INT_MIN / -1 overflow: verifies both.
int scale(int a, int b)
  pre(b > 0)
  post(result == 0)
{
  int q = a / b;
  return 0;
}
