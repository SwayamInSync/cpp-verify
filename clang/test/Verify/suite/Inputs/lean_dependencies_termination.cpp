cppverify::spec int scaled(int a, int b)
  cppverify::decreases(a * b)
{
  return a <= 0 || b <= 0 ? 0 : scaled(a, b - 1) + a;
}

int user()
  cppverify::post(cppverify::result == scaled(2, 1))
{
  return 2;
}

int wrong()
  cppverify::post(cppverify::result == 1)
{
  return 0;
}
