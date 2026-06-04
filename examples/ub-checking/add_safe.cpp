// Bounding the operands discharges the overflow obligation: verifies both ways.
int add(int a, int b)
  pre(a >= 0 && a <= 1000 && b >= 0 && b <= 1000)
  post(result == a + b)
{
  return a + b;
}
