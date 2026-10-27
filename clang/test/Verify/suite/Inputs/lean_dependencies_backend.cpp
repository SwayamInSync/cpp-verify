int next(int x)
  cppverify::post(cppverify::result == 7);

int seven(int x)
  cppverify::post(cppverify::result == 7)
{
  return next(x);
}

[[cppverify::trusted]] int assumed(int x)
  cppverify::post(cppverify::result == 7);

int trusting(int x)
  cppverify::post(cppverify::result == 7)
{
  return assumed(x);
}

int impossible(int x)
  cppverify::pre(x > 0 && x < 0)
  cppverify::post(cppverify::result == 7)
{
  return 0;
}

int same(int x)
  cppverify::decreases(*)
  cppverify::post(cppverify::result == x)
{
  return x;
}

int positive(int x)
  cppverify::pre(x > 0)
  cppverify::post(cppverify::result == x)
{
  return x;
}

int unchecked() { return positive(1); }

int countdown(int n)
  cppverify::post(true)
{
  while (n > 0)
    cppverify::invariant(true)
  {
    n = 0;
  }
  return n;
}
