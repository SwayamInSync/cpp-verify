// Negating INT_MIN overflows: verification fails with x = INT_MIN.
int negate(int x)
  cppverify::post(cppverify::result == -x)
{
  return -x;
}
