// Under a small resource limit Z3 proves only the trivial return check.
cppverify::proof void bump(int x)
  cppverify::pre(0 <= x && x <= 100)
{
  int y = x + 1;
  cppverify::check(y > x);
}
