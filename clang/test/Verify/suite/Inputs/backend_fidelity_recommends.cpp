spec int recommended_identity(int value)
  recommends(value >= 0)
{
  return value;
}

int recommendation_satisfied(int value)
  pre(value >= 0)
  post(result == value)
{
  return recommended_identity(value);
}

int recommendation_violated()
  post(result == 0)
{
  return recommended_identity(-1);
}
