// Loops for a bounded archive, for lean_replay.test: one ends within the
// bound, one need not.

int sum_small(int n)
  cppverify::pre(0 <= n && n <= 2)
  cppverify::post(cppverify::result >= 0)
{
  int s = 0;
  for (int i = 0; i < n; i = i + 1)
    s = s + i;
  return s;
}

int count_up(int n)
  cppverify::pre(0 <= n && n <= 1000)
  cppverify::post(cppverify::result == n)
{
  int c = 0;
  while (c < n)
    c = c + 1;
  return c;
}
