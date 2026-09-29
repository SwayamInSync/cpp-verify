spec int recommended_identity(int value)
  recommends(value >= 0)
{
  return value;
}

int recommendation_satisfied(int value)
  pre(value >= 0)
  post(result == recommended_identity(value))
{
  return value;
}

int recommendation_violated()
  post(result == recommended_identity(-1))
{
  return 0;
}
