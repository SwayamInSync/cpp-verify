[[cppverify::trusted]] unsigned kept(unsigned x)
  cppverify::post(cppverify::result == x);

unsigned product(unsigned a, unsigned b)
  cppverify::pre(a < 1000 && b < 1000)
  cppverify::decreases(*)
  cppverify::post(cppverify::result == a * b)
{
  return kept(a * b);
}

unsigned six()
  cppverify::post(cppverify::result == 6)
{
  return product(2, 3);
}

unsigned unchecked() { return product(1, 1); }

unsigned looping(unsigned a, unsigned b)
  cppverify::pre(a < 1000 && b < 1000)
  cppverify::post(cppverify::result == a * b)
{
  unsigned n = 0;
  while (n < 1)
  {
    n = 1;
  }
  return a * b;
}
