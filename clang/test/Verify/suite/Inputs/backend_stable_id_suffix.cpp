int two_invariants(int n)
  pre(n >= 0 && n <= 10)
{
  int i = 0;
  while (i < n)
    invariant(0 <= i)
    invariant(i < 0)
    decreases(n - i)
  {
    i = i + 1;
  }
  return i;
}
