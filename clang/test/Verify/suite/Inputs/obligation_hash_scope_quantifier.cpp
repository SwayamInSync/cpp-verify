int obligation_hash_scope(int x)
  cppverify::pre(x >= 0)
  cppverify::post(cppverify::result >= 0)
{
  cppverify::check(x >= 0);
  cppverify::check(cppverify::forall(i, 0, x, i >= 0));
  return x;
}
