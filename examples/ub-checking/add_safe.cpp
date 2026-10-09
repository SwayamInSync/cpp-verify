// Bounding the operands discharges the overflow obligation: verifies.
int add(int a, int b)
  cppverify::pre(a >= 0 && a <= 1000 && b >= 0 && b <= 1000)
  cppverify::post(cppverify::result == a + b)
{
  return a + b;
}
