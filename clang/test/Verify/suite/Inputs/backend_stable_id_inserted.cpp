int stable_identity(int value)
  cppverify::post(cppverify::result == 0)
{
  cppverify::check(value == value);
  return value;
}
