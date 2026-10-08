cppverify::spec int alpha(int x)
  cppverify::decreases(x)
{
  if (x <= 0)
    return 0;
  return 1 + alpha(x - 1);
}

cppverify::spec int bravo(int x)
  cppverify::decreases(x)
{
  if (x <= 0)
    return 0;
  return 1 + bravo(x - 1);
}

cppverify::proof void alpha_fuel_one()
  cppverify::post(alpha(0) == 0)
{
  cppverify::reveal_with_fuel(alpha, 1);
}

cppverify::proof void two_logical_functions()
  cppverify::post(alpha(1) + bravo(1) == 2)
{
  cppverify::reveal_with_fuel(alpha, 2);
  cppverify::reveal_with_fuel(bravo, 2);
}
