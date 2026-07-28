spec int alpha(int x)
  decreases(x)
{
  if (x <= 0)
    return 0;
  return 1 + alpha(x - 1);
}

spec int bravo(int x)
  decreases(x)
{
  if (x <= 0)
    return 0;
  return 1 + bravo(x - 1);
}

proof void alpha_fuel_one()
  post(alpha(0) == 0)
{
  reveal_with_fuel(alpha, 1);
}

proof void two_logical_functions()
  post(alpha(1) + bravo(1) == 2)
{
  reveal_with_fuel(alpha, 2);
  reveal_with_fuel(bravo, 2);
}
