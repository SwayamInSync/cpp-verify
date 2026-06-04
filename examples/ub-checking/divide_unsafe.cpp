// The quotient is unused, so this verifies WITHOUT --check-ub.
// WITH --check-ub it fails: no precondition rules out b == 0.
int scale(int a, int b)
  post(result == 0)
{
  int q = a / b;
  return 0;
}
