void needs_both(int n)
  pre(n >= 0)
  pre(n > 100)
{
}

void two_preconditions(int n)
  pre(n >= 0 && n <= 10)
{
  needs_both(n);
}
