void nonnegative(int n)
  cppverify::pre(cppverify::forall(k, 0, n, k >= 0) && n < 8)
{
}

void small()
  cppverify::post(true)
{
  nonnegative(3);
}
