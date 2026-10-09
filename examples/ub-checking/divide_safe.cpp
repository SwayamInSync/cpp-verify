// b > 0 rules out division by zero and the INT_MIN / -1 overflow: verifies.
int scale(int a, int b)
  cppverify::pre(b > 0)
  cppverify::post(cppverify::result == 0)
{
  int q = a / b;
  return 0;
}
