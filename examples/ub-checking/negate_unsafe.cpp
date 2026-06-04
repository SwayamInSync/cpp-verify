// WITHOUT --check-ub: verifies (under wrapping, -INT_MIN == INT_MIN).
// WITH --check-ub: fails -- negating INT_MIN overflows.
int negate(int x)
  post(result == -x)
{
  return -x;
}
