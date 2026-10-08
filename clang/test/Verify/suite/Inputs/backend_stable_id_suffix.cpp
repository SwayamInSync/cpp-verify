void needs_both(int n)
  cppverify::pre(n >= 0)
  cppverify::pre(n > 100)
{
}

void two_preconditions(int n)
  cppverify::pre(n >= 0 && n <= 10)
{
  needs_both(n);
}
