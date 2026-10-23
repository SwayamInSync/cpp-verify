int early()
  cppverify::post(cppverify::result == 2)
{
  return 1;
}

int fine()
  cppverify::post(cppverify::result == 1)
{
  return 1;
}
