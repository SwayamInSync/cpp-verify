// Excluding INT_MIN makes negation safe: verifies.
int negate(int x)
  cppverify::pre(x > -2147483648)
  cppverify::post(cppverify::result == -x)
{
  return -x;
}
