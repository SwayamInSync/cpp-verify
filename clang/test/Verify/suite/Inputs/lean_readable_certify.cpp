[[cppverify::trusted]] int next(int x)
  cppverify::pre(x < 100)
  cppverify::post(cppverify::result == x + 1);

int twice(int x)
  cppverify::pre(x >= 0 && x < 50)
  cppverify::post(cppverify::result == x + 2)
{
  int a = next(x);
  int b = next(a);
  return b;
}
