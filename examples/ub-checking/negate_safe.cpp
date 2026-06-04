// Excluding INT_MIN makes negation safe: verifies both ways.
int negate(int x)
  pre(x > -2147483648)
  post(result == -x)
{
  return -x;
}
