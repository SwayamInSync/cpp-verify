unsigned a_slow()
  cppverify::post(cppverify::result == 0)
{
  unsigned u = 2;
  return u << 31;
}

int next(int x)
  cppverify::pre(x >= 0 && x < 100)
  cppverify::post(cppverify::result == x + 1)
{
  return x + 1;
}

int square(int x)
  cppverify::pre(x >= 0 && x < 1000)
  cppverify::post(cppverify::result >= 0)
{
  return x * x;
}
