// C++ division and remainder in contracts, for lean_division.test.

cppverify::proof void half_bound(int a)
  cppverify::pre(a >= 4)
  cppverify::post(a / 2 >= 2 && a % 2 >= 0)
{
}

cppverify::proof void negative_division(int a)
  cppverify::pre(a < 0 && a > -100)
  cppverify::post(a / 2 <= 0 && a % 3 <= 0)
{
}
