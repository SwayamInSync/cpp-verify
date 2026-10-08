cppverify::spec int recommended_identity(int value)
  cppverify::recommends(value >= 0)
{
  return value;
}

int recommendation_satisfied(int value)
  cppverify::pre(value >= 0)
  cppverify::post(cppverify::result == recommended_identity(value))
{
  return value;
}

int recommendation_violated()
  cppverify::post(cppverify::result == recommended_identity(-1))
{
  return 0;
}
