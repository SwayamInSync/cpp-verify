// The quotient is unused, but evaluating a / b is undefined for b == 0, and
// no precondition rules that out: verification fails with b = 0.
int scale(int a, int b)
  cppverify::post(cppverify::result == 0)
{
  int q = a / b;
  return 0;
}
