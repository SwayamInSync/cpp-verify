cppverify::spec int tri(int n)
  cppverify::decreases(n)
{
  return n <= 0 ? 0 : tri(n - 1) + n;
}

int six_again()
  cppverify::post(cppverify::result == tri(3))
{
  cppverify::reveal_with_fuel(tri, 4);
  return 6;
}

int one_again()
  cppverify::post(cppverify::result == 1)
  cppverify::post(cppverify::result >= 0)
  cppverify::post(cppverify::result == 1)
{
  return 1;
}
