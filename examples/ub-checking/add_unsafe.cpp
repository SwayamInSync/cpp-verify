// result == a + b holds under wrapping, so this verifies WITHOUT --check-ub.
// WITH --check-ub it fails: a + b can overflow (signed overflow is UB).
int add(int a, int b)
  post(result == a + b)
{
  return a + b;
}
