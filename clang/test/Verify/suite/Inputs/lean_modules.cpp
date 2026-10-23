// Five functions for lean_modules.test: inc and dbl, and two that apply the
// recursive spec tri, whose postconditions Inputs/lean_modules_*.lean also
// prove by hand.

cppverify::spec int tri(int n)
  cppverify::decreases(n)
{
  return n <= 0 ? 0 : tri(n - 1) + n;
}

int inc(int x)
  cppverify::pre(0 <= x && x < 1000)
  cppverify::post(cppverify::result == x + 1)
{
  return x + 1;
}

int dbl(int x)
  cppverify::pre(0 <= x && x < 1000)
  cppverify::post(cppverify::result == 2 * x)
{
  return x + x;
}

int tri_zero()
  cppverify::post(cppverify::result == tri(0))
{
  return 0;
}

int plus_tri_zero(int x)
  cppverify::pre(0 <= x && x < 1000)
  cppverify::post(cppverify::result == x + tri(0))
{
  return x;
}
